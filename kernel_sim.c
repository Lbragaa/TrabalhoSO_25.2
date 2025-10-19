// kernel_sim.c — signals=wake-ups, pipes=data; no mem*; one read per wake; TICK+snapshot.
// RR with explicit ready FIFO:
// - IRQ0: running -> tail, head -> running (single-line log)
// - IRQ1/2: unblock -> tail (always log unblocked/enqueued; if IDLE, dispatch next)
// - SYSCALL by runner: runner -> BLOCKED (not enqueued), schedule next
//
// Other fixes preserved:
// - IC signal handlers at file scope
// - Apps ignore SIGINT so Ctrl-C only pauses kernel/IC
// - Kernel reaps IC, closes FDs on exit
// - Device queues reset indices when empty

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <signal.h>
#include <string.h>
#include <time.h>
#include <sys/wait.h>
#include <errno.h>

#define N_APPS 5
#define MAX_BLOCKED N_APPS
#define MAX_READY   N_APPS
#define QUANTUM_US  500000   // 0.5s

enum ProcState { READY=0, RUNNING=1, BLOCKED=2, TERMINATED=3 };

struct PCB {
    pid_t pid;
    int   id;           // 1..N_APPS
    int   state;        // enum ProcState
    int   pc;           // last known PC
    int   last_dev;     // 0/1/2
    char  last_op;      // 'R'/'W'/'X' or '\0'
    int   cnt_d1;
    int   cnt_d2;
};

static struct PCB pcbs[N_APPS];
static int running_idx = -1;

// ---- device wait queues (per device) ----
static pid_t qd1[MAX_BLOCKED], qd2[MAX_BLOCKED];
static int hd1=0, td1=0, hd2=0, td2=0;

// ---- READY queue (global RR FIFO) ----
static int rq[MAX_READY];
static int rq_h=0, rq_t=0, rq_sz=0;

static int inter_r = -1, app_r = -1;
static pid_t inter_pid = -1;

// wake flags
static volatile sig_atomic_t inter_pending = 0;
static volatile sig_atomic_t app_pending   = 0;
// pause/resume control (kernel)
static volatile sig_atomic_t want_snapshot = 0;
static volatile sig_atomic_t want_resume   = 0;
static int paused = 0;

// --- InterController local pause flag + handlers at file scope
static volatile sig_atomic_t ic_paused = 0;
static void ic_h_int (int s){ (void)s; ic_paused = 1; }
static void ic_h_cont(int s){ (void)s; ic_paused = 0; }

// ----- small helpers (no mem*) -----
static int acc_append(char acc[], int acc_cap, int *acc_len, const char src[], int n){
    int copied = 0;
    while (copied < n && *acc_len < acc_cap){ acc[*acc_len] = src[copied]; (*acc_len)++; copied++; }
    return copied;
}
static int acc_find_nl(const char acc[], int len){ for (int i=0;i<len;i++) if (acc[i]=='\n') return i; return -1; }
static void acc_copy_line(const char acc[], int linelen, char dest[], int dest_cap){
    int k = linelen; if (k >= dest_cap) k = dest_cap-1; for (int i=0;i<k;i++) dest[i]=acc[i]; dest[k]='\0';
}
static void acc_consume_line(char acc[], int *acc_len, int linelen){
    int new_len = *acc_len - (linelen+1); if (new_len < 0) new_len = 0;
    for (int i=0;i<new_len;i++) acc[i] = acc[linelen+1+i]; *acc_len = new_len;
}

// ----- misc -----
static void die(const char *m){ perror(m); exit(1); }
static ssize_t writeln(int fd, const char *s){ return write(fd, s, strlen(s)); }
static const char* st_str(int s){ return s==READY?"READY":s==RUNNING?"RUNNING":s==BLOCKED?"BLOCKED":s==TERMINATED?"TERMINATED":"?"; }
static int pid_to_index(pid_t pid){ for (int i=0;i<N_APPS;i++) if (pcbs[i].pid==pid) return i; return -1; }

// ----- READY queue ops -----
static void rq_push_tail(int idx){
    if (rq_sz >= MAX_READY) return; // shouldn't happen with N_APPS cap
    rq[rq_t] = idx;
    rq_t = (rq_t+1) % MAX_READY;
    rq_sz++;
}
static int rq_pop_head(void){
    if (rq_sz==0) return -1;
    int idx = rq[rq_h];
    rq_h = (rq_h+1) % MAX_READY;
    rq_sz--;
    return idx;
}

// Central scheduler: pick next from READY queue (if any), else idle
static void schedule_next(void){
    // NEW: pop until we find a truly READY task; drop stale BLOCKED/TERMINATED entries.
    int tries = rq_sz;           // upper bound: at most current size pops
    while (tries-- > 0){
        int next = rq_pop_head();
        if (next < 0) break;
        if (pcbs[next].state == READY){
            if (running_idx >= 0 && pcbs[running_idx].state==RUNNING){
                kill(pcbs[running_idx].pid, SIGSTOP);
                pcbs[running_idx].state = READY;
            }
            kill(pcbs[next].pid, SIGCONT);
            pcbs[next].state = RUNNING;
            running_idx = next;
            fprintf(stderr,"[Kernel] Now running A%d (PID %d)\n", next+1, pcbs[next].pid);
            return;
        }
        // else: stale entry (BLOCKED/TERMINATED) — skip it and continue
    }

    // none READY → idle
    if (running_idx >= 0 && pcbs[running_idx].state==RUNNING){
        kill(pcbs[running_idx].pid, SIGSTOP);
        pcbs[running_idx].state = READY;
    }
    running_idx = -1;
    fprintf(stderr,"[Kernel] IDLE (no READY)\n");
}

// ----- kernel signal handlers -----
static void h_usr1(int s){ (void)s; inter_pending = 1; }
static void h_usr2(int s){ (void)s; app_pending   = 1; }
static void h_int (int s){ (void)s; want_snapshot = 1; } // Ctrl-C
static void h_cont(int s){ (void)s; want_resume   = 1; } // SIGCONT

// ----- snapshot -----
static void print_snapshot(void){
    fprintf(stderr, "================ SNAPSHOT (paused) ================\n");
    for (int i=0;i<N_APPS;i++){
        struct PCB *p = &pcbs[i];
        fprintf(stderr, "A%d (PID %d): PC=%d, state=%s", p->id, (int)p->pid, p->pc, st_str(p->state));
        if (p->state == BLOCKED){
            if (p->last_dev==1 || p->last_dev==2) fprintf(stderr, ", waiting D%d %c", p->last_dev, (p->last_op?p->last_op:'?'));
            else fprintf(stderr, ", waiting D?");
        }
        fprintf(stderr, ", counts: D1=%d, D2=%d", p->cnt_d1, p->cnt_d2);
        if (p->state == TERMINATED) fprintf(stderr, " (TERMINATED)");
        fprintf(stderr, "\n");
    }
    fprintf(stderr, "READY Q: ");
    if (rq_sz==0) fprintf(stderr, "(empty)\n");
    else {
        for (int k=0, p=rq_h; k<rq_sz; k++, p=(p+1)%MAX_READY){
            int idx = rq[p];
            fprintf(stderr, "A%d ", idx+1);
        }
        fprintf(stderr, "\n");
    }
    if (running_idx>=0) fprintf(stderr, "RUNNING: A%d\n", running_idx+1);
    else fprintf(stderr, "RUNNING: (none)\n");
    fprintf(stderr, "===================================================\n");
}

// ------------------ Children ------------------

static void run_app(int id){
    signal(SIGINT, SIG_IGN);
    raise(SIGSTOP);
    srand((unsigned)(time(NULL) ^ getpid()));
    int pc = 0, MAX_PC = 20;

    while (pc < MAX_PC){
        sleep(1);
        pc++;

        // TICK
        char tick[64]; int tn = snprintf(tick,sizeof(tick),"TICK A%d %d %d\n", id, getpid(), pc);
        write(STDOUT_FILENO, tick, tn);
        kill(getppid(), SIGUSR2);

        // ~10% chance of syscall; op ∈ {R,W,X}
        if (rand()%10 == 0){
            int dev = (rand()%2) + 1;
            char ops[3] = {'R','W','X'};
            char op = ops[rand()%3];
            char msg[96];
            int n = snprintf(msg,sizeof(msg),"SYSCALL A%d %d D%d %c\n", id, getpid(), dev, op);
            write(STDOUT_FILENO, msg, n);
            kill(getppid(), SIGUSR2);
            raise(SIGSTOP);
        }
    }
    char done[64]; int dn = snprintf(done,sizeof(done),"DONE A%d %d %d\n", id, getpid(), pc);
    write(STDOUT_FILENO, done, dn); kill(getppid(), SIGUSR2);
    _exit(0);
}

static void run_interrupt_controller(void){
    signal(SIGINT,  ic_h_int);
    signal(SIGCONT, ic_h_cont);

    srand((unsigned)(time(NULL) ^ getpid()));
    for(;;){
        if (ic_paused){ usleep(100000); continue; }
        usleep(QUANTUM_US);
        writeln(STDOUT_FILENO, "IRQ0\n"); kill(getppid(), SIGUSR1);
        if (rand()%10 == 0){ writeln(STDOUT_FILENO,"IRQ1\n"); kill(getppid(), SIGUSR1); }
        if (rand()%20 == 0){ writeln(STDOUT_FILENO,"IRQ2\n"); kill(getppid(), SIGUSR1); }
    }
}

// ------------------ Kernel Readers ------------------

static void drain_inter(void){
    static char acc[1024]; static int acc_len=0;
    char buf[256];
    ssize_t n = read(inter_r, buf, sizeof(buf));
    if (n <= 0){ if (n < 0 && errno == EINTR) return; return; }
    acc_append(acc, (int)sizeof(acc), &acc_len, buf, (int)n);
    if (acc_len >= (int)sizeof(acc)) acc_len = 0;

    for(;;){
        int pos = acc_find_nl(acc, acc_len); if (pos < 0) break;
        char line[128]; acc_copy_line(acc, pos, line, (int)sizeof(line)); acc_consume_line(acc, &acc_len, pos);

        if (strcmp(line,"IRQ0")==0){
            // Timeslice: demote current to tail (if exists), pick next (single-line)
            if (running_idx >= 0 && pcbs[running_idx].state==RUNNING){
                int cur = running_idx;
                pcbs[cur].state = READY;
                rq_push_tail(cur);
                kill(pcbs[cur].pid, SIGSTOP);
                running_idx = -1;
            }
            int next = rq_pop_head();
            if (next >= 0){
                // guard: only dispatch if truly READY; else keep popping
                if (pcbs[next].state == READY){
                    kill(pcbs[next].pid, SIGCONT);
                    pcbs[next].state = RUNNING;
                    running_idx = next;
                    fprintf(stderr,"[Kernel] IRQ0 -> Now running A%d (PID %d)\n", next+1, pcbs[next].pid);
                } else {
                    // stale; rely on schedule_next to complete selection
                    rq_push_tail(next); // optional: drop instead; here we requeue then call scheduler
                    schedule_next();
                }
            } else {
                fprintf(stderr,"[Kernel] IRQ0 -> IDLE (no READY)\n");
            }
        } else if (strcmp(line,"IRQ1")==0){
            if (hd1 < td1){
                pid_t pid = qd1[hd1++]; int idx = pid_to_index(pid);
                if (hd1 == td1) { hd1 = td1 = 0; }  // reset when empty
                if (idx>=0 && pcbs[idx].state!=TERMINATED){
                    pcbs[idx].state = READY;
                    rq_push_tail(idx);
                    fprintf(stderr,"[Kernel] IRQ1 -> unblocked A%d (PID %d) enqueued\n", idx+1, pid);
                    if (running_idx == -1) schedule_next(); // will print "Now running ..."
                }
            }
        } else if (strcmp(line,"IRQ2")==0){
            if (hd2 < td2){
                pid_t pid = qd2[hd2++]; int idx = pid_to_index(pid);
                if (hd2 == td2) { hd2 = td2 = 0; }  // reset when empty
                if (idx>=0 && pcbs[idx].state!=TERMINATED){
                    pcbs[idx].state = READY;
                    rq_push_tail(idx);
                    fprintf(stderr,"[Kernel] IRQ2 -> unblocked A%d (PID %d) enqueued\n", idx+1, pid);
                    if (running_idx == -1) schedule_next(); // will print "Now running ..."
                }
            }
        } else {
            fprintf(stderr,"[Kernel] Unknown IRQ: '%s'\n", line);
        }
    }
}

static void drain_apps(void){
    static char acc[4096]; static int acc_len=0;
    char buf[512];
    ssize_t n = read(app_r, buf, sizeof(buf));
    if (n <= 0){ if (n < 0 && errno == EINTR) return; return; }
    acc_append(acc, (int)sizeof(acc), &acc_len, buf, (int)n);
    if (acc_len >= (int)sizeof(acc)) acc_len = 0;

    for(;;){
        int pos = acc_find_nl(acc, acc_len); if (pos < 0) break;
        char line[512]; acc_copy_line(acc, pos, line, (int)sizeof(line)); acc_consume_line(acc, &acc_len, pos);

        if (strncmp(line,"TICK", 4)==0){
            int aid, pid, pc;
            if (sscanf(line, "TICK A%d %d %d", &aid, &pid, &pc)==3){
                int idx = pid_to_index((pid_t)pid);
                if (idx>=0 && pcbs[idx].state != TERMINATED) pcbs[idx].pc = pc;
            }
        } else if (strncmp(line,"SYSCALL",7)==0){
            int aid, pid, dev; char op;
            if (sscanf(line,"SYSCALL A%d %d D%d %c", &aid, &pid, &dev, &op)==4){
                int idx = pid_to_index((pid_t)pid);
                if (idx>=0 && pcbs[idx].state!=TERMINATED){
                    pcbs[idx].state = BLOCKED; pcbs[idx].last_dev = dev; pcbs[idx].last_op  = op;
                    if (dev==1){ pcbs[idx].cnt_d1++; if (td1<MAX_BLOCKED) qd1[td1++] = (pid_t)pid; }
                    else if (dev==2){ pcbs[idx].cnt_d2++; if (td2<MAX_BLOCKED) qd2[td2++] = (pid_t)pid; }

                    if (idx == running_idx){
                        kill(pcbs[idx].pid, SIGSTOP);
                        running_idx = -1;
                        fprintf(stderr,"[Kernel] SYSCALL A%d (PID %d): D%d %c -> BLOCKED\n", idx+1, pid, dev, op);
                        schedule_next();
                    } else {
                        fprintf(stderr,"[Kernel] SYSCALL A%d (PID %d): D%d %c -> BLOCKED (wasn't running)\n", idx+1, pid, dev, op);
                    }
                }
            }
        } else if (strncmp(line,"DONE",4)==0){
            int aid, pid, pc;
            if (sscanf(line,"DONE A%d %d %d",&aid,&pid,&pc)==3){
                int idx = pid_to_index((pid_t)pid);
                if (idx>=0){
                    pcbs[idx].pc = pc; pcbs[idx].state = TERMINATED;
                    fprintf(stderr,"[Kernel] A%d (PID %d) TERMINATED (PC=%d)\n", idx+1, pid, pc);
                    if (idx == running_idx){
                        running_idx = -1;
                        schedule_next();
                    }
                }
            }
        } else {
            fprintf(stderr,"[Kernel] Unknown app msg: '%s'\n", line);
        }
    }
}

// ------------------ Kernel main ------------------

static void run_kernel(void){
    fprintf(stderr, "[Kernel] PID=%d\n", getpid());

    int inter_p[2], app_p[2];
    if (pipe(inter_p)==-1 || pipe(app_p)==-1) die("pipe");

    // spawn InterController
    inter_pid = fork(); if (inter_pid == -1) die("fork inter");
    if (inter_pid == 0){
        close(inter_p[0]);
        if (dup2(inter_p[1], STDOUT_FILENO)==-1) die("dup2 inter");
        close(inter_p[1]); close(app_p[0]); close(app_p[1]);
        execlp("./kernel_sim","kernel_sim","inter",NULL); die("exec inter");
    }

    // spawn apps
    for (int i=0;i<N_APPS;i++){
        pid_t p = fork(); if (p == -1) die("fork app");
        if (p == 0){
            close(app_p[0]);
            if (dup2(app_p[1], STDOUT_FILENO)==-1) die("dup2 app");
            close(app_p[1]); close(inter_p[0]); close(inter_p[1]);
            char idstr[8]; int m = snprintf(idstr,sizeof(idstr), "%d", i+1); (void)m;
            execlp("./kernel_sim","kernel_sim","app", idstr, NULL); die("exec app");
        }
        pcbs[i].pid=p; pcbs[i].id=i+1; pcbs[i].state=READY; pcbs[i].pc=0;
        pcbs[i].last_dev=0; pcbs[i].last_op='\0'; pcbs[i].cnt_d1=pcbs[i].cnt_d2=0;
    }

    close(inter_p[1]); close(app_p[1]); inter_r = inter_p[0]; app_r = app_p[0];

    signal(SIGUSR1, h_usr1); signal(SIGUSR2, h_usr2);
    signal(SIGINT,  h_int ); signal(SIGCONT, h_cont);

    // Build initial READY queue: all apps; start A1
    rq_h=rq_t=rq_sz=0;
    for (int i=0;i<N_APPS;i++) rq_push_tail(i);
    running_idx = -1;
    schedule_next(); // starts A1

    fprintf(stderr,"[Kernel] Started. Running A1 (PID %d)\n", pcbs[0].pid);

    for(;;){
        pause();

        if (want_snapshot){
            want_snapshot = 0; paused = 1;
            if (inter_pid > 0) kill(inter_pid, SIGINT);
            if (running_idx >= 0 && pcbs[running_idx].state==RUNNING)
                kill(pcbs[running_idx].pid, SIGSTOP);
            print_snapshot();
        }
        if (want_resume){
            want_resume = 0; paused = 0;
            if (inter_pid > 0) kill(inter_pid, SIGCONT);
            if (running_idx >= 0 && pcbs[running_idx].state==RUNNING)
                kill(pcbs[running_idx].pid, SIGCONT);
            fprintf(stderr,"[Kernel] Resumed.\n");
        }

        if (!paused){
            if (inter_pending){ inter_pending = 0; drain_inter(); }
            if (app_pending)  { app_pending   = 0; drain_apps();  }
        }

        // reap children
        int status; pid_t r;
        while ((r = waitpid(-1, &status, WNOHANG)) > 0){
            int idx = pid_to_index(r);
            if (idx >= 0 && pcbs[idx].state != TERMINATED){
                pcbs[idx].state = TERMINATED;
                fprintf(stderr,"[Kernel] (reap) A%d (PID %d) TERMINATED\n", idx+1, (int)r);
                if (idx == running_idx){
                    running_idx = -1;
                    schedule_next();
                }
            }
        }

        int alive = 0; for (int i=0;i<N_APPS;i++) if (pcbs[i].state != TERMINATED){ alive=1; break; }
        if (!alive){
            if (inter_pid > 0){ kill(inter_pid, SIGTERM); waitpid(inter_pid, NULL, 0); }
            if (inter_r >= 0) close(inter_r);
            if (app_r   >= 0) close(app_r);
            fprintf(stderr,"[Kernel] All apps terminated. Exiting.\n");
            break;
        }
    }
}

int main(int argc, char *argv[]){
    if (argc == 1){ run_kernel(); return 0; }
    if (argc >= 2 && strcmp(argv[1],"inter")==0){ run_interrupt_controller(); return 0; }
    if (argc >= 3 && strcmp(argv[1],"app")==0){
        int id = atoi(argv[2]); if (id<1 || id>N_APPS) id=1; run_app(id); return 0;
    }
    fprintf(stderr,"Usage:\n  ./kernel_sim               (kernel)\n  ./kernel_sim inter         (interrupt controller)\n  ./kernel_sim app <id>      (app)\n");
    return 1;
}
