// nucleo_sim.c
// Simulador simples de Núcleo + Controlador de Interrupções + Apps (A1..A5)
// RR com quantum fixo; Apps fazem "SYSCALL" que as bloqueia em D1/D2;
// Controlador gera IRQ0 (timer) e, aleatoriamente, IRQ1/IRQ2 (liberação de D1/D2).
// Tudo com strings em PT-BR para diferenciar do seu projeto.

#define _POSIX_C_SOURCE 200809L
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <signal.h>
#include <string.h>   // strcmp, strncmp
#include <time.h>
#include <sys/wait.h>
#include <errno.h>

/* ----------------- Parâmetros ----------------- */
#define QTD_APPS       5
#define MAX_BLOQ       64
#define QUANTUM_US     400000  /* 0.4s, só pra ver o RR girando */

/* ----------------- Estados ----------------- */
typedef enum { PRONTO=0, EXECUTANDO=1, BLOQUEADO=2, ENCERRADO=3 } Estado;

/* ----------------- PCB ----------------- */
typedef struct {
    pid_t pid;
    int   aid;    /* A1..A5 => 1..5 */
    Estado estado;
} PCB;

/* ----------------- "Estruturas" do Núcleo ----------------- */
static PCB   pcbs[QTD_APPS];
static int   idx_exe = -1;

static pid_t filaD1[MAX_BLOQ], filaD2[MAX_BLOQ];
static int   hd1=0, td1=0, hd2=0, td2=0;

static int fd_irq_r = -1, fd_app_r = -1;

static volatile sig_atomic_t tem_irq = 0;
static volatile sig_atomic_t tem_app = 0;

/* ----------------- Utilitários ----------------- */
static void falha(const char *m){ perror(m); _exit(1); }

static int pcb_por_pid(pid_t p){
    for (int i=0;i<QTD_APPS;i++) if (pcbs[i].pid==p) return i;
    return -1;
}

/* --------- Acumuladores de linha (sem usar memmove) --------- */
static int acc_append(char acc[], int cap, int *len, const char *src, int n){
    int c=0; while(c<n && *len<cap) acc[(*len)++]=src[c++]; return c;
}
static int acc_find_nl(const char acc[], int len){
    for (int i=0;i<len;i++) if (acc[i]=='\n') return i; return -1;
}
static void acc_copy_line(const char acc[], int linelen, char dst[], int cap){
    int k = linelen<cap-1? linelen: cap-1;
    for (int i=0;i<k;i++) dst[i]=acc[i]; dst[k]='\0';
}
static void acc_consume_line(char acc[], int *len, int linelen){
    int novo = *len - (linelen+1); if (novo<0) novo=0;
    for(int i=0;i<novo;i++) acc[i]=acc[linelen+1+i];
    *len = novo;
}

/* ----------------- Escalonador RR ----------------- */
static int proximo_pronto(int atual){
    for (int passo=1; passo<=QTD_APPS; passo++){
        int i = (atual<0)? (passo-1)%QTD_APPS : (atual+passo)%QTD_APPS;
        if (pcbs[i].estado==PRONTO) return i;
    }
    return -1;
}

static void log_troca(int antes, int depois){
    if (depois>=0){
        if (antes==depois)
            fprintf(stderr,"[NUC] Continua A%d (PID %d)\n", depois+1, pcbs[depois].pid);
        else if (antes>=0)
            fprintf(stderr,"[NUC] Troca: A%d -> A%d (PID %d)\n", antes+1, depois+1, pcbs[depois].pid);
        else
            fprintf(stderr,"[NUC] Troca: OCIOSO -> A%d (PID %d)\n", depois+1, pcbs[depois].pid);
    } else {
        if (antes>=0) fprintf(stderr,"[NUC] Troca: A%d -> OCIOSO\n", antes+1);
        else          fprintf(stderr,"[NUC] Permanece OCIOSO\n");
    }
}

/* Faz a troca de contexto "lógica": SIGSTOP no anterior e SIGCONT no novo */
static void troca_contexto(int escolhido){
    int ant = idx_exe;

    if (escolhido>=0){
        if (idx_exe!=escolhido){
            if (idx_exe>=0 &&
                pcbs[idx_exe].estado!=BLOQUEADO &&
                pcbs[idx_exe].estado!=ENCERRADO){
                kill(pcbs[idx_exe].pid, SIGSTOP);
                pcbs[idx_exe].estado = PRONTO;
            }
            kill(pcbs[escolhido].pid, SIGCONT);
            pcbs[escolhido].estado = EXECUTANDO;
            idx_exe = escolhido;
        }
    } else {
        if (idx_exe>=0 &&
            pcbs[idx_exe].estado!=BLOQUEADO &&
            pcbs[idx_exe].estado!=ENCERRADO){
            kill(pcbs[idx_exe].pid, SIGSTOP);
            pcbs[idx_exe].estado = PRONTO;
        }
        idx_exe = -1;
    }

    log_troca(ant, idx_exe);
}

/* ----------------- Tratadores de Sinal ----------------- */
static void on_usr1(int s){ (void)s; tem_irq = 1; }
static void on_usr2(int s){ (void)s; tem_app = 1; }

/* ======================================================== */
/* =================== PROCESSO: APP ====================== */
/* ======================================================== */
static void exec_app(int aid){
    /* Aguardar ser CPU-bound pela 1ª vez */
    raise(SIGSTOP);

    srand((unsigned)(time(NULL) ^ getpid()));
    int pc = 0, LIM = 20;

    while (pc < LIM){
        /* Trabalho "CPU" */
        usleep(120000);
        pc++;

        /* 12% de chance de fazer uma "chamada de sistema" */
        if (rand()%100 < 12){
            int disp = (rand()%2)+1;   /* D1 ou D2 */
            char op  = (rand()%2==0)? 'L' : 'E'; /* Ler/Escrever */

            char msg[96];
            int n = snprintf(msg,sizeof(msg),
                             "SYSCALL A%d %d D%d %c\n", aid, getpid(), disp, op);
            (void)write(STDOUT_FILENO, msg, n);

            /* Avisa o núcleo que chegou linha das apps */
            kill(getppid(), SIGUSR2);

            /* Bloqueia-se até o núcleo reescalonar */
            raise(SIGSTOP);
        }
    }

    /* Terminei */
    {
        char fim[64];
        int n = snprintf(fim,sizeof(fim), "FIM A%d %d\n", aid, getpid());
        (void)write(STDOUT_FILENO, fim, n);
        kill(getppid(), SIGUSR2);
    }
    _exit(0);
}

/* ======================================================== */
/* ===== PROCESSO: CONTROLADOR DE INTERRUPÇÕES (CINT) ===== */
/* ======================================================== */
static void exec_cint(void){
    srand((unsigned)(time(NULL) ^ getpid()));
    for(;;){
        /* Tick do temporizador (IRQ0) */
        usleep(QUANTUM_US);
        (void)write(STDOUT_FILENO, "IRQ0\n", 5);
        kill(getppid(), SIGUSR1);

        /* Libera D1/D2 aleatoriamente */
        if (rand()%8==0){
            (void)write(STDOUT_FILENO, "IRQ1\n", 5);
            kill(getppid(), SIGUSR1);
        }
        if (rand()%15==0){
            (void)write(STDOUT_FILENO, "IRQ2\n", 5);
            kill(getppid(), SIGUSR1);
        }
    }
}

/* ======================================================== */
/* ============= Leitura/Tratamento de mensagens ========== */
/* ======================================================== */
static void trata_irq(const char *linha){
    if (strcmp(linha,"IRQ0")==0){
        int prox = proximo_pronto(idx_exe);
        if (prox>=0) troca_contexto(prox);
        else {
            if (idx_exe>=0 && pcbs[idx_exe].estado==EXECUTANDO){
                fprintf(stderr,"[NUC] IRQ0: mantém A%d (PID %d)\n",
                        idx_exe+1, pcbs[idx_exe].pid);
            } else {
                troca_contexto(-1);
            }
        }
    }
    else if (strcmp(linha,"IRQ1")==0){
        if (hd1<td1){
            pid_t p = filaD1[hd1++];
            int i = pcb_por_pid(p);
            if (i>=0 && pcbs[i].estado!=ENCERRADO){
                pcbs[i].estado = PRONTO;
                fprintf(stderr,"[NUC] IRQ1: A%d liberada de D1 (PID %d)\n", i+1, p);
                if (idx_exe<0) troca_contexto(i);
            }
        }
    }
    else if (strcmp(linha,"IRQ2")==0){
        if (hd2<td2){
            pid_t p = filaD2[hd2++];
            int i = pcb_por_pid(p);
            if (i>=0 && pcbs[i].estado!=ENCERRADO){
                pcbs[i].estado = PRONTO;
                fprintf(stderr,"[NUC] IRQ2: A%d liberada de D2 (PID %d)\n", i+1, p);
                if (idx_exe<0) troca_contexto(i);
            }
        }
    }
    else {
        fprintf(stderr,"[NUC] IRQ desconhecida: '%s'\n", linha);
    }
}

static void trata_apps(const char *linha){
    if (strncmp(linha,"SYSCALL",7)==0){
        int aid,pid,disp; char op;
        if (sscanf(linha,"SYSCALL A%d %d D%d %c", &aid,&pid,&disp,&op)==4){
            int i = pcb_por_pid((pid_t)pid);
            if (i<0 || pcbs[i].estado==ENCERRADO) return;

            pcbs[i].estado = BLOQUEADO;
            if      (disp==1 && td1<MAX_BLOQ) filaD1[td1++] = (pid_t)pid;
            else if (disp==2 && td2<MAX_BLOQ) filaD2[td2++] = (pid_t)pid;

            if (i==idx_exe){
                int prox = proximo_pronto(idx_exe);
                if (prox>=0){
                    troca_contexto(prox);
                    fprintf(stderr,"[NUC] SYSCALL A%d (PID %d): D%d %c → BLOQ; agora A%d\n",
                            i+1,pid,disp,op,idx_exe+1);
                } else {
                    troca_contexto(-1);
                    fprintf(stderr,"[NUC] SYSCALL A%d (PID %d): D%d %c → BLOQ; OCIOSO\n",
                            i+1,pid,disp,op);
                }
            } else {
                fprintf(stderr,"[NUC] SYSCALL A%d (PID %d): D%d %c → BLOQ\n",
                        i+1,pid,disp,op);
            }
        } else {
            fprintf(stderr,"[NUC] Linha SYSCALL inválida: '%s'\n", linha);
        }
    }
    else if (strncmp(linha,"FIM",3)==0){
        int aid,pid;
        if (sscanf(linha,"FIM A%d %d", &aid,&pid)==2){
            int i = pcb_por_pid((pid_t)pid);
            if (i>=0){
                pcbs[i].estado = ENCERRADO;
                fprintf(stderr,"[NUC] A%d (PID %d) ENCERRADA\n", i+1, pid);
                if (i==idx_exe){
                    int prox = proximo_pronto(idx_exe);
                    if (prox>=0) troca_contexto(prox);
                    else troca_contexto(-1);
                }
            }
        } else {
            fprintf(stderr,"[NUC] Linha FIM inválida: '%s'\n", linha);
        }
    }
    else {
        fprintf(stderr,"[NUC] Msg APP desconhecida: '%s'\n", linha);
    }
}

static void drenar_irq(void){
    static char acc[1024]; static int alen=0;
    char buf[256];
    ssize_t n = read(fd_irq_r, buf, sizeof(buf));
    if (n<=0){ if (n<0 && errno!=EINTR){} return; }
    (void)acc_append(acc,(int)sizeof(acc),&alen,buf,(int)n);
    if (alen>=(int)sizeof(acc)) alen=0; /* proteção tosca */

    for(;;){
        int pos = acc_find_nl(acc, alen);
        if (pos<0) break;
        char linha[128];
        acc_copy_line(acc, pos, linha, (int)sizeof(linha));
        acc_consume_line(acc, &alen, pos);
        trata_irq(linha);
    }
}

static void drenar_apps(void){
    static char acc[4096]; static int alen=0;
    char buf[512];
    ssize_t n = read(fd_app_r, buf, sizeof(buf));
    if (n<=0){ if (n<0 && errno!=EINTR){} return; }
    (void)acc_append(acc,(int)sizeof(acc),&alen,buf,(int)n);
    if (alen>=(int)sizeof(acc)) alen=0;

    for(;;){
        int pos = acc_find_nl(acc, alen);
        if (pos<0) break;
        char linha[512];
        acc_copy_line(acc, pos, linha, (int)sizeof(linha));
        acc_consume_line(acc, &alen, pos);
        trata_apps(linha);
    }
}

/* ======================================================== */
/* ===================== Núcleo (pai) ===================== */
/* ======================================================== */
static void executar_nucleo(void){
    int p_irq[2], p_app[2];
    if (pipe(p_irq)==-1 || pipe(p_app)==-1) falha("pipe");

    /* Controlador de Interrupções */
    pid_t pid_cint = fork();
    if (pid_cint==-1) falha("fork cint");
    if (pid_cint==0){
        close(p_irq[0]);              /* vai escrever em p_irq[1] */
        if (dup2(p_irq[1], STDOUT_FILENO)==-1) falha("dup2 cint");
        close(p_irq[1]);
        close(p_app[0]); close(p_app[1]);
        execlp("./nucleo_sim","nucleo_sim","cint",NULL);
        falha("exec cint");
    }

    /* Apps A1..A5 */
    for (int i=0;i<QTD_APPS;i++){
        pid_t p = fork();
        if (p==-1) falha("fork app");
        if (p==0){
            close(p_app[0]);           /* vai escrever em p_app[1] */
            if (dup2(p_app[1], STDOUT_FILENO)==-1) falha("dup2 app");
            close(p_app[1]);
            close(p_irq[0]); close(p_irq[1]);
            char id[8]; snprintf(id,sizeof(id), "%d", i+1);
            execlp("./nucleo_sim","nucleo_sim","app", id, NULL);
            falha("exec app");
        }
        pcbs[i].pid = p; pcbs[i].aid = i+1; pcbs[i].estado = PRONTO;
    }

    /* Núcleo só fica com as pontas de leitura */
    close(p_irq[1]); close(p_app[1]);
    fd_irq_r = p_irq[0]; fd_app_r = p_app[0];

    /* Sinais para acordar o núcleo e ler UMA vez os pipes */
    struct sigaction sa1 = {0}, sa2 = {0};
    sa1.sa_handler = on_usr1; sigemptyset(&sa1.sa_mask); sa1.sa_flags = 0;
    sa2.sa_handler = on_usr2; sigemptyset(&sa2.sa_mask); sa2.sa_flags = 0;
    sigaction(SIGUSR1, &sa1, NULL);
    sigaction(SIGUSR2, &sa2, NULL);

    /* Começa executando A1 */
    troca_contexto(0);
    fprintf(stderr,"[NUC] Boot: rodando A1 (PID %d)\n", pcbs[0].pid);

    for(;;){
        pause();  /* acorda com USR1/USR2 */

        if (tem_irq){ tem_irq=0; drenar_irq(); }
        if (tem_app){ tem_app=0; drenar_apps(); }

        /* Recolhe filhos (evita zumbis) */
        int st; pid_t r;
        while((r=waitpid(-1,&st,WNOHANG))>0){
            int i = pcb_por_pid(r);
            if (i>=0 && pcbs[i].estado!=ENCERRADO){
                pcbs[i].estado = ENCERRADO;
                fprintf(stderr,"[NUC] (reap) A%d (PID %d) ENCERRADA\n", i+1, (int)r);
                if (i==idx_exe){
                    int prox = proximo_pronto(idx_exe);
                    if (prox>=0) troca_contexto(prox);
                    else troca_contexto(-1);
                }
            }
        }

        /* Sai quando todas as apps acabarem */
        int alguma=0;
        for (int i=0;i<QTD_APPS;i++) if (pcbs[i].estado!=ENCERRADO){alguma=1;break;}
        if (!alguma){
            fprintf(stderr,"[NUC] Todas apps encerradas. Saindo.\n");
            break;
        }
    }
}

/* ======================================================== */
/* ========================= main ========================= */
/* ======================================================== */
int main(int argc, char *argv[]){
    if (argc==1){ executar_nucleo(); return 0; }

    if (argc>=2 && strcmp(argv[1],"cint")==0){
        exec_cint();
        return 0;
    }
    if (argc>=3 && strcmp(argv[1],"app")==0){
        int aid = atoi(argv[2]); if (aid<1 || aid>QTD_APPS) aid=1;
        exec_app(aid);
        return 0;
    }

    fprintf(stderr,
        "Uso:\n"
        "  ./nucleo_sim             # núcleo\n"
        "  ./nucleo_sim cint        # controlador de interrupções\n"
        "  ./nucleo_sim app <id>    # app (1..%d)\n", QTD_APPS);
    return 1;
}
