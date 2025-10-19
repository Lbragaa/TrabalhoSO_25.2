#include <stdio.h>
#include <stdlib.h>
#include <unistd.h> // fork(), pipe(), read(), write(), close()
#include <signal.h> // signal(), kill()
#include <sys/wait.h> // waitpid()
#include <time.h> //  time()
#include <string.h> // strcpy()
#include <errno.h> //  (errno), EAGAIN(erro de recurso não disponível em leitura não bloqueante), EWOULDBLOCK (erro similar)
#include <fcntl.h> // fcntl(), F_GETFL, F_SETFL, O_NONBLOCK (para pipes não bloqueantes)
#include <sys/select.h> // select()


// Configurações
#define NUM_PROCS_APP 5 
#define MAX_ITERATIONS 20 // máximo de iterações por App antes de terminar
#define TIMESLICE_MS 500 // em milissegundos
#define true 1
#define false 0

// Probabilidades 
#define PROB_SYSCALL 10 // a cada iteração, chance de fazer syscall por parte de um procesos
#define P1_PROB 10 // probabilidade de IRQ1 (dispositivo 1) a cada timeslice
#define P2_PROB 5  // probabilidade de IRQ2 (dispositivo 2) a cada timeslice

// Tipos e enums
typedef enum {
    IRQ_TIMESLICE = 0, // IRQ0
    IRQ_IO_D1 = 1, // IRQ1
    IRQ_IO_D2 = 2  // IRQ2
} InterruptType;

typedef enum {
    READY,
    RUNNING,
    BLOCKED,
    TERMINATED
} ProcessState;

typedef enum { 
    DEVICE_D1 = 0, 
    DEVICE_D2 = 1 
} Device;
typedef enum { 
    OP_READ = 0, 
    OP_WRITE = 1, 
    OP_EXEC = 2 
} Operation;


// Mensagens InterController -> Kernel e Apps -> Kernel
typedef struct {
    int type; // qual foi o InterruptType enviado pelo InterController
} IRQMsg;

typedef enum { 
    APP_SYSCALL = 1, // chamada de sis
    APP_TERMINATED = 2, // processo terminou (loop concluido)
    APP_PROGRESS = 3 // PC incrementado
} AppMsgType; // tipos de mensagem de que os application process enviam para o Kernel

typedef struct {
    int type;  // AppMsgType
    pid_t pid; // remetente
    int device; // Device (se for syscall)
    int op; // Operation (se for syscall)
} AppMsg;



// PCBs e Tabelas
typedef struct {
    pid_t pid;
    char name[3]; // nome do processo
    ProcessState state;
    int pc; // program counter do processo 

    // bloqueio
    int blocked_dev; // -1 se não bloqueado
    int blocked_op;  // válido se bloqueado

    // contadores por operação
    int count_read;
    int count_write;
    int count_exec;

    int alive; // se o filho ainda existe (não reaproveitado)
} PCB;

// Filas para gerenciamento de PIDS
#define QMAX 5 // tamanho máximo das filas de PIDs  

typedef struct {
    pid_t data[QMAX];
    int head, tail, size;
} PIDQueue; //struct da fila de PIDs

void q_init(PIDQueue *q){ 
    q->head = q->tail = q->size = 0; 
}
int q_empty(PIDQueue *q){ 
    if (q->size == 0) 
        return true;
    return false;
}
int q_full (PIDQueue *q){ 
    if (q->size == QMAX) 
        return true;
    return false;
}
int q_push (PIDQueue *q, pid_t v){
    if(q_full(q)) 
        return false; // não consegue enfileirar porque já esta cheio
    q->data[q->tail] = v; // coloca o pid depois do último atual
    q->tail = (q->tail + 1) % QMAX; // atualiza o tail circularmente
    q->size++; // aumenta o tamanho
    return true; // retorna true por ter conseguido enfileirar
}
int q_pop(PIDQueue *q){ // a função retorna o pid que ela retirou 
    if(q_empty(q)) 
        return -1; // não consegue desenfileirar porque já esta vazio
    pid_t v = q->data[q->head];
    q->head = (q->head + 1) % QMAX; // atualiza o head circularmente
    q->size--;
    return v; // retorna o pid que foi retirado
}

// Variáveis globais
PCB pcb[NUM_PROCS_APP]; // tabela de PCBs
PIDQueue ready_q;
PIDQueue blocked_d1_q;
PIDQueue blocked_d2_q;

int irq_pipe[2], sys_pipe[2]; // pipes de comunicação 

//Função que retorna o índice do PID na tabela de PCB, se não achar, retorna -1
int app_index_from_pid(pid_t p){
    for(int i=0;i<NUM_PROCS_APP;i++) {
        if(pcb[i].pid == p) 
            return i;
    }
    return -1;
}

int got_sigint = 0; // flag para verificar se recebeu SIGINT por Ctrl+C

//Função para setar a flag de recebimento de sigint como 1, confirmando que recebeu o sinal vindo de Ctrl+C
void sigint_handler(int sig){ 
    got_sigint = 1; 
}

void sigusr1_handler(int sig){ // o sinal sigusr1 é enviado quando queremos pausar o kernel devido a um Ctrl+C
     //apenas acorda pause/select 
}

// Funções para retornar strings de estados, dispositivos e operações
char* state_str(ProcessState s){
    switch(s){
        case READY: 
            return "READY";
        case RUNNING: 
            return "RUNNING";
        case BLOCKED: 
            return "BLOCKED";
        case TERMINATED: 
            return "TERMINATED";
    }
}
char* dev_str(int d){ 
    if (d==0)
        return "D1";
    return "D2";
}

char* op_str(int op){
    switch(op){ 
        case OP_READ: 
            return "READ"; 
        case OP_WRITE: 
            return "WRITE"; 
        case OP_EXEC: 
            return "EXEC"; 
    }
}

// Função para setar um pipe como não bloqueante 
void set_nonblock(int fd){
    int flags = fcntl(fd, F_GETFL, 0); // pega as flags atuais
    fcntl(fd, F_SETFL, flags | O_NONBLOCK); // adiciona a flag de não bloqueante
}

//Função para imprimir a tabela de status dos processos. é chamada quando a flag de sigint está como 1. 
//A função fprintf é usada para imprimir no stderr,
void print_status_table(){
    printf("\n===== STATUS (Kernel PID = %d) =====\n", getpid());
    printf(" PID     | Name |   State   |  PC  | Blocked | Op   | R  W  X \n");
    printf("--------------------------------------------------------------\n");
    for(int i=0;i<NUM_PROCS_APP;i++){
        PCB *p = &pcb[i];
        printf(" %-7d | %-4s | %-9s | %-4d | ", p->pid, p->name, state_str(p->state), p->pc);
        if(p->state == BLOCKED){
            printf("%-7s | %-4s | ", dev_str(p->blocked_dev), op_str(p->blocked_op));
        } else {
            printf("%-7s | %-4s | ", "-", "-");
        }
        printf("%-2d %-2d %-2d\n", p->count_read, p->count_write, p->count_exec);
    }
    printf(" ReadyQ size=%d | D1Q=%d | D2Q=%d\n", ready_q.size, blocked_d1_q.size, blocked_d2_q.size);
    printf("================================\n\n");
}

// Função para trocar o processo em execução
int current_pid = -1;

// Enfileira o processo antigo (se aplicável) e troca para next_pid
void switch_to(pid_t next_pid){
    int nidx = app_index_from_pid(next_pid);
    // Pare o atual e re-enfileire se ainda estiver RUNNING
    if(current_pid > 0){
        int idx = app_index_from_pid(current_pid);

        if(idx >= 0 && pcb[idx].state == RUNNING){
            //Para o processo atual, seta seu estado como READY e o enfileira novamente na fila de prontos
            kill(current_pid, SIGSTOP);
            pcb[idx].state = READY;
            q_push(&ready_q, current_pid);

            printf("[Kernel] Troca -> %s (fim do timeslice de %s)\n", pcb[nidx].name, pcb[idx].name);
            
        }
    }

    // Inicia/continua o próximo
    if(nidx >= 0 && pcb[nidx].state == READY){
        pcb[nidx].state = RUNNING;
        current_pid = next_pid;
        kill(next_pid, SIGCONT);
        printf("[Kernel] Executando %s\n", pcb[nidx].name);
       
        
    }
}

// InterController 
void intercontroller_process(){
    close(irq_pipe[0]); // fecha leitura
    // Fechar sys_pipe no IC
    close(sys_pipe[0]); close(sys_pipe[1]);

    IRQMsg m; //Struct para envio de mensagens de IRQ
    int r; // número aleatório
    // semente aleatória para geração de números aleatórios
    srand((unsigned)time(NULL));


    while(1){
        usleep(TIMESLICE_MS * 1000); // espera o tempo do timeslice
        m.type = IRQ_TIMESLICE; // gera o timeslice
        if(write(irq_pipe[1], &m, sizeof(m)) < 0){
            // Kernel pode ter morrido; encerra
            exit(0);
        }

        // Gera IRQ1/IRQ2 de acordo com a probabilidade
        r = rand()%100;
        if(r < P1_PROB){
            m.type = IRQ_IO_D1;
            write(irq_pipe[1], &m, sizeof(m));
        }

        r = rand()%100;
        if(r < P2_PROB){
            m.type = IRQ_IO_D2;
            write(irq_pipe[1], &m, sizeof(m));
        }

    }
}

// --------------- App ---------------
static void app_process(int app_no){
    // app_no em 0..NUM_PROCS_APP-1
    // Fechar descritores que não usa
    close(irq_pipe[0]); close(irq_pipe[1]); // apps não usam IRQ pipe
    close(sys_pipe[0]); // app só escreve

    int r;
    // semente aleatória por processo
    srand(time(NULL)  ^  getpid());

    int pc = 0;
    while(pc < MAX_ITERATIONS){
        sleep(1); // 1 seg

        // Chance de syscall
        r = rand()%100;
        if(r < PROB_SYSCALL){
            // escolhe device/op
            Device d;
            if (rand() % 2 == 0)
                d = DEVICE_D1;
            
            else
                d = DEVICE_D2;
            int opraw = rand()%3;
            Operation op = (Operation)opraw;

            AppMsg msg;
            msg.device = (int)d;
            msg.type = APP_SYSCALL;
            msg.pid = getpid();
            msg.op = (int)op; 
            write(sys_pipe[1], &msg, sizeof(msg));

            // Envia um sigstop para si mesmo. Kernel decidirá o que vai fazer
            kill(getpid(), SIGSTOP);
            
        } else {
            // avança PC
            pc++;
            AppMsg progress;
            progress.type = APP_PROGRESS;
            progress.pid = getpid();
            progress.device = -1;
            progress.op = pc;
            write(sys_pipe[1], &progress, sizeof(progress));
        }
    }

    // terminou
    AppMsg done;
    done.type = APP_TERMINATED;
    done.pid = getpid();
    done.device = -1;
    done.op = -1;
    write(sys_pipe[1], &done, sizeof(done));
    exit(0);
}

// --------------- Kernel (Main) ---------------
int main(void){
    // Instala sinais para status/pause/retomar
    signal(SIGINT,  sigint_handler);
    signal(SIGUSR1, sigusr1_handler);
    signal(SIGCONT, sigusr1_handler);

    if(pipe(irq_pipe) < 0 || pipe(sys_pipe) < 0){
        printf("Erro na criação dos pipes\n");
        exit(1);
    }

    
    // Colocar leitura como não bloqueante dos pipes 
    set_nonblock(irq_pipe[0]);
    set_nonblock(sys_pipe[0]);

    // Cria InterController
    pid_t ic_pid = fork();
    if(ic_pid < 0){ 
        printf("Erro na criação do InterControllerSIM\n");
        exit(1);
    }
    if(ic_pid == 0){
        intercontroller_process();
        exit(0);
    }

    // Fecha escrita de IRQ no Kernel; quem escreve é só o IC
    close(irq_pipe[1]);

    // Cria as filas de pronto, bloqueado em D1 e bloqueado em D2
    q_init(&ready_q);
    q_init(&blocked_d1_q);
    q_init(&blocked_d2_q);

    //Criaçao dos processos
    for(int i=0;i<NUM_PROCS_APP;i++){
        char name[3], number_to_chr;
        number_to_chr = (char)i + 49;
        name[0] = 'A';
        name[1] = number_to_chr;
        name[2] = '\0';
        strcpy(pcb[i].name, name);
        pcb[i].state = READY;
        pcb[i].pc = 0;
        pcb[i].blocked_dev = -1;
        pcb[i].blocked_op = -1;
        pcb[i].count_read = pcb[i].count_write = pcb[i].count_exec = 0;
        pcb[i].alive = false;

        pid_t p = fork();
        if(p < 0){
            printf("Erro na criação dos processos\n");
            exit(1);
        }
        if(p == 0){
            // Os application processes começam parados, e são escalonados quando o kernel decidir
            // Para isso: mandar SIGSTOP a si mesmo, Kernel fará SIGCONT quando escalar
            kill(getpid(), SIGSTOP);
            app_process(i);
            return 0;
        }
        // No Kernel: registra PCB e enfileira
        pcb[i].pid = p;
        pcb[i].alive = true;
        q_push(&ready_q, p);
        printf("[Kernel] %s PID=%d pronto\n", pcb[i].name, p);
        
    }

    // Kernel não escreve no sys_pipe; só lê
    close(sys_pipe[1]);

    // Começa executando o primeiro pronto
    if(!q_empty(&ready_q)){
        pid_t first = q_pop(&ready_q);
        int fidx = app_index_from_pid(first);
        if(fidx >= 0) pcb[fidx].state = READY;
        switch_to(first);
    }

    // Loop principal do Kernel
    int apps_terminated = 0;
    fd_set rds; // estrutura usada por select() para indicarmos quais file descriptors (pipes) queremos monitorar 
    int nfds = (irq_pipe[0] > sys_pipe[0] ? irq_pipe[0] : sys_pipe[0]) + 1; // define o maior numero de descritor que queremos avaliar + 1

    while(1){
        if(apps_terminated >= NUM_PROCS_APP){
            printf("[Kernel] Todos os apps terminaram.\n");
            // Encerra IC e sai
            kill(ic_pid, SIGKILL);
            waitpid(ic_pid, NULL, 0);
            break;
        }

        if(got_sigint){
            got_sigint = 0;
            print_status_table();
            pause();
        }

        FD_ZERO(&rds); 
        FD_SET(irq_pipe[0], &rds); // coloca os pipes dentro da estrutura de seleção
        FD_SET(sys_pipe[0], &rds);

        // Espera algo chegar (IRQ0/1/2 ou SYSCALL/TERM)
        int rv = select(nfds, &rds, NULL, NULL, NULL); // o select ordena o kernel a esperar até que possua alguma mensagem em algum dos pipes definidos com FD_SET para ler. enquanto isso, o kernel "dorme"
        if(rv < 0){ // se o tempo de espera acabou e nada ficou pronto
            if(errno == EINTR) // se ele foi interrompido por um sinal (como Ctrl+C, apenas passa a próxima iteração do loop)
                continue;
            printf("Erro na leitura dos pipes\n");
            break;
        }

        // 1) Mensagens de Apps (syscalls / terminated)
        if(FD_ISSET(sys_pipe[0], &rds)){ // verifica se alguma mensagem no pipe de syscall foi enviada
            while (1){
                AppMsg am;
                int n = read(sys_pipe[0], &am, sizeof(am));
                if(n < 0){
                    if(errno==EAGAIN || errno==EWOULDBLOCK) // se o read falhou pq nao tem mais nada pra ler(pipe vazio), volta pro loop principal do kernel
                        break;
                    printf("Erro na leitura do pipe de syscall\n"); // aqui, é necessário que a estrutura e funcionamento do pipe esteja quebrada
                    break;
                }
                if(n == 0) // se o escritor fechou, volta para o loop principal.
                    break;

                if(am.type == APP_SYSCALL){ // se for syscall
                    int idx = app_index_from_pid(am.pid);
                    if(idx >= 0 && pcb[idx].state != TERMINATED){
                        // marca bloqueado e contabiliza
                        pcb[idx].state = BLOCKED;
                        pcb[idx].blocked_dev = am.device;
                        pcb[idx].blocked_op  = am.op;
                        if(am.op == OP_READ) 
                            pcb[idx].count_read++;
                        else if(am.op == OP_WRITE) 
                            pcb[idx].count_write++;
                        else if(am.op == OP_EXEC) 
                            pcb[idx].count_exec++;

                        // Remove de running se era o atual
                        if(current_pid == am.pid){
                            current_pid = -1;
                        }

                        // coloca na fila do dispositivo
                        if(am.device == DEVICE_D1) 
                            q_push(&blocked_d1_q, am.pid);
                        else 
                            q_push(&blocked_d2_q, am.pid);

                        printf( "[Kernel] %s fez SYSCALL %s em %s, agora BLOQUEADO\n", pcb[idx].name, op_str(am.op), dev_str(am.device));
                        

                        // Escalone imediatamente outro se houver
                        if(!q_empty(&ready_q)){
                            pid_t next = q_pop(&ready_q);
                            int nidx = app_index_from_pid(next);
                            if(nidx >= 0 && pcb[nidx].state == READY){
                                switch_to(next);
                            }
                        }
                    }
                } else if(am.type == APP_TERMINATED){ // se o app terminou 
                    int idx = app_index_from_pid(am.pid);
                    if(idx >= 0 && pcb[idx].state != TERMINATED){
                        pcb[idx].state = TERMINATED;
                        pcb[idx].alive = false;
                        if(current_pid == am.pid) 
                            current_pid = -1;
                        apps_terminated++;
                        printf("[Kernel] %s terminou.\n", pcb[idx].name);
                        // escalar o próximo
                        if(!q_empty(&ready_q)){
                            pid_t next = q_pop(&ready_q);
                            int nidx = app_index_from_pid(next);
                            if(nidx >= 0 && pcb[nidx].state == READY){
                                switch_to(next);
                            }
                        }
                    }
                } else if (am.type == APP_PROGRESS) { // se for uma mensagem  de progresso (atualização de PC)
                    int idx = app_index_from_pid(am.pid);
                    if (idx >= 0 && pcb[idx].state != TERMINATED) {
                        pcb[idx].pc = am.op; // atualiza o PC
                    }
                }
            }
        }

        // 2) Mensagens de IRQ (IRQ0/1/2)
        if(FD_ISSET(irq_pipe[0], &rds)){ //verifica se o pipe de leitura de irq do kernel possui algum conteúdo
            while(1){
                IRQMsg im;
                int n = read(irq_pipe[0], &im, sizeof(im));
                if(n < 0){
                    if(errno==EAGAIN || errno==EWOULDBLOCK) // se o pipe estiver vazio, volta para o loop principal
                        break;
                    printf("Erro na leitura do pipe de IRQs\n");
                    break;
                }
                if(n == 0) //se o escritor fechou, volta para loop principal do kernel
                    break;

                if(im.type == IRQ_TIMESLICE){
                    // pegar o proximo e trocar 
                    if(!q_empty(&ready_q)){
                        pid_t next = q_pop(&ready_q);
                        int nidx = app_index_from_pid(next);
                        if(nidx >= 0){
                            // Garante que next esteja marcado READY
                            if(pcb[nidx].state == READY){
                                switch_to(next);
                            }
                        }
                    } 
                } else if(im.type == IRQ_IO_D1 || im.type == IRQ_IO_D2){
                    PIDQueue *bq;
                    if (im.type == IRQ_IO_D1)
                        bq = &blocked_d1_q;
                    else
                        bq = &blocked_d2_q;
                    if(!q_empty(bq)){ // se não estiver vazia, libera o processo na primeira posição da  fila
                        pid_t unb = q_pop(bq);
                        int uidx = app_index_from_pid(unb);
                        if(uidx >= 0 && pcb[uidx].state == BLOCKED){
                            pcb[uidx].state = READY;
                            pcb[uidx].blocked_dev = -1;
                            pcb[uidx].blocked_op  = -1;
                            q_push(&ready_q, unb);
                            printf( "[Kernel] IRQ %s: desbloqueou %s\n", (im.type==IRQ_IO_D1?"D1":"D2"), pcb[uidx].name);
                            
                        }
                    }
                }
            }
        }

        //Recolhe apps que já estão terminated
        while(1){
            int status;
            int w = waitpid(-1, &status, WNOHANG); // espera qualquer filho terminar. se ninguém terminou, não bloquear o kernel (WNOHANG)
            if(w <= 0) 
                break;
        }
    }

    // encerra qualquer resto de processo que ainda não tenha terminado
    for(int i=0;i<NUM_PROCS_APP;i++){
        if(pcb[i].alive){
            kill(pcb[i].pid, SIGKILL);
            waitpid(pcb[i].pid, NULL, 0);
        }
    }
    return 0;
}