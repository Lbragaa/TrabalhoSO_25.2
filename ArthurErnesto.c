#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <sys/wait.h>
#include <signal.h>
#include <time.h>
#include <string.h>
#include <errno.h> // Adicionado para o tratamento de erros
#include <fcntl.h>


// Constantes 
#define NUM_PROCS_APP 5
#define MAX_ITERATIONS 20
#define TIMESLICE_MS 500
#define PROB_SYSCALL 15 // Probabilidade de 15% de gerar uma syscall
#define P1_PROB 10   // Probabilidade de IRQ1
#define P2_PROB 5   // Probabilidade de IRQ2

// Tipos de interrupção
typedef enum {
    IRQ_TIMESLICE = 0, // IRQ0
    IRQ_IO_D1 = 1,     // IRQ1
    IRQ_IO_D2 = 2      // IRQ2
} InterruptType;

// Estados dos processos
typedef enum {
    READY,
    RUNNING,
    BLOCKED,
    TERMINATED
} ProcessState;

// Dispositivos e Operações
typedef enum { DEVICE_D1, DEVICE_D2 } Device;
typedef enum { OP_READ, OP_WRITE, OP_EXEC } Operation;

// Estrutura para uma chamada de sistema (syscall) com campo de contexto (PC)
typedef struct {
    pid_t pid;
    int pc; // Campo para o Program Counter
    Device device;
    Operation operation;
} SyscallRequest;

// Estrutura do Bloco de Controle de Processo (PCB)
typedef struct {
    pid_t pid; // pid do processo
    ProcessState state; // estado do processo
    int pc; // Program Counter
    int d1_access_count; // Contador de acessos ao dispositivo D1
    int d2_access_count; // Contador de acessos ao dispositivo D2
    Device blocked_on_device; // dispositivo em que está bloqueado(se aplicável)
    Operation blocked_on_operation; // operação em que está bloqueado(se aplicável)
} PCB;


// --- VARIÁVEIS GLOBAIS ---
PCB process_table[NUM_PROCS_APP]; // Tabela de processos
pid_t kernel_pid, inter_controller_pid; // PIDs do Kernel e do InterController
pid_t ready_queue_processes[NUM_PROCS_APP]; // Fila de processos prontos
int total_ready_processes = 0; // Numero de processos na fila de prontos
int irq_pipe[2]; // pipe para comunicação de IRQs
int syscall_pipe[2];// pipe para comunicação de syscalls 
int display_status_flag = 0; // Flag para exibir o status

// --- FUNÇÕES AUXILIARES E HANDLERS DE SINAL ---
// Adiciona um PID ao final da fila de prontos
void enqueue_ready(pid_t pid) {

    if (total_ready_processes < NUM_PROCS_APP) {
        ready_queue_processes[total_ready_processes++] = pid;
    }
}

// Remove e retorna um PID do início da fila de prontos
pid_t dequeue_ready() {
    if (total_ready_processes == 0) {
        return 0; // Retorna 0 se a fila estiver vazia
    }
    pid_t pid = ready_queue_processes[0];
    for (int i = 0; i < total_ready_processes - 1; i++) {
        ready_queue_processes[i] = ready_queue_processes[i + 1];
    }
    total_ready_processes--;
    return pid;
}
char* state_to_str(ProcessState state) {
    if (state == READY) 
        return "Pronto";
    else if (state == RUNNING) 
        return "Executando";
    else if (state == BLOCKED) 
        return "Bloqueado";
    return "Terminado";
}
char* device_to_str(Device dev) {
    if (dev == DEVICE_D1) 
        return "D1";
    return "D2";
}
char* op_to_str(Operation op) {
    if (op == OP_READ) 
        return "R";
    else if (op == OP_WRITE) 
        return "W";
    return "X";
}

void sigint_handler(int signum) {
    if (getpid() == kernel_pid) {
        display_status_flag = 1; // Seta a flag para exibir o status
    }
}

// CORREÇÃO DEFINITIVA: O handler DEVE ser vazio.
void sigusr1_handler(int signum) {
    // Esta função é intencionalmente vazia. Sua única finalidade
    // é interromper a chamada 'read()' bloqueante no loop do kernel.
    // Qualquer código aqui, especialmente exit(), causa o término do programa.
}

void display_process_status() {
    printf("\n--- ESTADO ATUAL DO SISTEMA ---\n");
    printf("============================================================================================\n");
    printf("| PID\t| Estado\t\t| PC\t| Acessos D1\t| Acessos D2\t| Bloqueado em\n");
    printf("--------------------------------------------------------------------------------------------\n");
    for (int i = 0; i < NUM_PROCS_APP; i++) {
        printf("| %d\t| %-22s\t| %d/%d\t| %d\t\t| %d\t\t|",
               process_table[i].pid,
               state_to_str(process_table[i].state),
               process_table[i].pc, MAX_ITERATIONS,
               process_table[i].d1_access_count,
               process_table[i].d2_access_count);
        
        if (process_table[i].state == BLOCKED) {
            printf(" %s (%s)\n", device_to_str(process_table[i].blocked_on_device), op_to_str(process_table[i].blocked_on_operation));
        } else {
            printf(" N/A\n");
        }
    }
    printf("============================================================================================\n");
    printf("Sistema pausado. Envie SIGCONT para o Kernel (PID: %d) para continuar.\n", (int)kernel_pid);
    printf("Comando: kill -SIGCONT %d\n\n", (int)kernel_pid);
}

// Lógica dos processos
void application_logic(int id, PCB *proc_PCB) {
    int pc = 0;
    srand(time(NULL) ^ getpid()); // Semente diferente para cada processo, para inicialização randômica
    int random_n;
    
    
    while (pc < MAX_ITERATIONS) {
        sleep(1);
        random_n = rand() % 100;
        InterruptType message_to_irq = -1;

    
        if (random_n < PROB_SYSCALL) {
            SyscallRequest req;
            req.pid = getpid();
            req.pc = pc; // Envia o contexto (PC) para o Kernel
            req.device = (rand() % 2 == 0) ? DEVICE_D1 : DEVICE_D2;    
            req.operation = (Operation)(rand() % 3);

            printf("[App %d - PID %d] Gerando syscall para %s, op %s no PC=%d\n", 
                   id + 1, getpid(), device_to_str(req.device), op_to_str(req.operation), pc);

            write(syscall_pipe[1], &req, sizeof(SyscallRequest));
            sleep(1); // espera o kernel reagir e bloquar esse processo
    
        }
        pc++;
        proc_PCB->pc++; // Atualiza o PC no PCB
        printf("[App %d - PID %d] Iteração %d de %d concluída.\n", id + 1, getpid(), pc, MAX_ITERATIONS);
    }
     printf("[App %d - PID %d] Terminou a execução.\n", id+1, getpid());
     exit(0);
}

void inter_controller_logic() {
    srand(time(NULL)); // Semente para geração randômica

    while (1) { // loop infinito
        usleep(TIMESLICE_MS * 1000); // Converte ms para us
        InterruptType irq = IRQ_TIMESLICE; // Sempre envia IRQ0 (timeslice)
        write(irq_pipe[1], &irq, sizeof(InterruptType));

        if ((rand() % 100) < P1_PROB) {
            irq = IRQ_IO_D1;
            write(irq_pipe[1], &irq, sizeof(InterruptType));
        }
        if ((rand() % 100) < P2_PROB) {
            irq = IRQ_IO_D2;
            write(irq_pipe[1], &irq, sizeof(InterruptType));
        }
    }
}


void kernel_logic() {
    kernel_pid = getpid(); // O Kernel precisa saber seu próprio PID
    pid_t blocked_queue_d1[NUM_PROCS_APP] = {0}; // Filas de bloqueados de D1
    pid_t blocked_queue_d2[NUM_PROCS_APP] = {0}; // Filas de bloqueados de D2
    int d1_q_size = 0, d2_q_size = 0; // Tamanhos das filas de bloqueados atual
    int current_running_idx = -1;
    int all_processes_terminated = 0;


    //Criando os processos
    for (int i = 0; i < NUM_PROCS_APP; i++) {
        pid_t pid = fork();
        if (pid == 0) {
            close(syscall_pipe[0]);
            close(irq_pipe[0]); 
            application_logic(i, process_table + i);
            close(irq_pipe[1]);
            exit(0);
        } else {
            process_table[i].pid = pid;
            process_table[i].state = READY;
            process_table[i].pc = 0;
            process_table[i].d1_access_count = 0;
            process_table[i].d2_access_count = 0;
            ready_queue_processes[total_ready_processes++] = pid;
            printf("[Kernel] Processo de aplicação A%d criado com PID %d e adicionado à fila de prontos.\n", i + 1, pid);
        }
    }
    close(syscall_pipe[1]); // Fecha a extremidade de escrita do pipe de syscalls no kernel
    // Inicialmente, todos os processos são pausados
    for(int i = 0; i < NUM_PROCS_APP; i++) {
        kill(ready_queue_processes[i], SIGSTOP);
    }
    
    current_running_idx = 0;
    process_table[current_running_idx].state = RUNNING;
    kill(process_table[current_running_idx].pid, SIGCONT);
    printf("[Kernel] Escalonando processo A%d (PID %d).\n", current_running_idx + 1, process_table[current_running_idx].pid);
    dequeue_ready(); // Remove o processo que está sendo executado da fila de prontos
    printf("Apos\n");
    for(int i = 0; i < total_ready_processes; i++){
        printf("Fila de prontos: PID %d\n", ready_queue_processes[i]);
    }

    while (1) {
        /*
        //PARTE CTRL  C ERRADA
        if (display_status_flag) {
            display_process_status();
            display_status_flag = 0;
            pause();
            printf("\n[Kernel] Retomando a execução...\n");
        }*/

        InterruptType received_irq;
        int bytes_read = read(irq_pipe[0], &received_irq, sizeof(InterruptType));

        if (bytes_read > 0) {
            printf("[Kernel] Recebeu IRQ%d.\n", received_irq);
            switch (received_irq) {
                case IRQ_TIMESLICE: {
                    if (current_running_idx != -1 && process_table[current_running_idx].state == RUNNING)  {

                        kill(process_table[current_running_idx].pid, SIGSTOP);

                        //Se o processo tiver terminado exatamente no timeslice, ele NÃO VAI para a fila de prontos
                        if (process_table[current_running_idx].pc >= MAX_ITERATIONS){
                            process_table[current_running_idx].state = TERMINATED;
                            printf("[Kernel] Processo A%d (PID %d) terminou sua execução.\n", current_running_idx + 1, process_table[current_running_idx].pid);
                        }

                        else{ // Adiciona o processo de volta na fila de prontos
                            process_table[current_running_idx].state = READY;
                            enqueue_ready(process_table[current_running_idx].pid);
                        }
                        
                        printf("[Kernel] Timeslice! Processo A%d (PID %d) foi interrompido.\n", current_running_idx + 1, process_table[current_running_idx].pid);
                        printf("Apos\n");
                        for(int i = 0; i < total_ready_processes; i++){
                            printf("Fila de prontos: PID %d\n", ready_queue_processes[i]);
                        }
                        //Descobrir a posição do próximo processo pronto na tabela de processos
                        current_running_idx = -1;
                        for (int i = 0; i < NUM_PROCS_APP; i++){
                            if (process_table[i].pid == ready_queue_processes[0]){
                                current_running_idx = i;
                                break;
                            }
                        }

                        if (current_running_idx == -1){
                            printf("[Kernel] Nenhum processo na fila de prontos para executar.\n");
                            break;
                        }
                        else{
                            dequeue_ready(); // remove o processo que será executado da fila de prontos
                            process_table[current_running_idx].state = RUNNING;
                            kill(process_table[current_running_idx].pid, SIGCONT);
                            printf("[Kernel] Contexto trocado para o processo A%d (PID %d).\n", current_running_idx + 1, process_table[current_running_idx].pid);
                        }
                
                    }
                    break;
                }


                case IRQ_IO_D1: { 

                    if (d1_q_size > 0){
                        printf("[Kernel] Dispositivo D1 liberado.");

                        for (int i = 0; i < NUM_PROCS_APP; i++){
                            if (process_table[i].pid == blocked_queue_d1[0]) {
                                printf("Desbloqueando processo A%d (PID %d).\n", i + 1, process_table[i].pid);
                                process_table[i].state = READY;
                                process_table[i].d1_access_count++;
                                enqueue_ready(process_table[i].pid);
                                //Retirando o processo da fila de bloqueados
                                for (int j = 1; j <  d1_q_size; j++) {
                                    blocked_queue_d1[j - 1] = blocked_queue_d1[j];
                                }
                                d1_q_size--;
                                break;
                            }
                        }
                    }

                    else{
                        printf("[Kernel] Dispositivo D1 liberado. Nenhum processo estava bloqueado.\n");
                    }
                    break; 
                }
                case IRQ_IO_D2: {
                    if (d2_q_size > 0){
                        printf("[Kernel] Dispositivo D2 liberado.");

                        for (int i = 0; i < NUM_PROCS_APP; i++){
                            if (process_table[i].pid == blocked_queue_d2[0]) {
                                printf("Desbloqueando processo A%d (PID %d).\n", i + 1, process_table[i].pid);
                                process_table[i].state = READY;
                                process_table[i].d2_access_count++;
                                enqueue_ready(process_table[i].pid);
                                //Retirando o processo da fila de bloqueados
                                for (int j = 1; j <  d2_q_size; j++) {
                                    blocked_queue_d2[j - 1] = blocked_queue_d2[j];
                                }
                                d2_q_size--;
                                break;
                            }
                        }
                    }

                    else{
                        printf("[Kernel] Dispositivo D2 liberado. Nenhum processo estava bloqueado.\n");
                    }
                    break; 
                }
            }
        }

        SyscallRequest syscall_req; 
        bytes_read = read(syscall_pipe[0], &syscall_req, sizeof(SyscallRequest));

        if (bytes_read > 0) { // Recebeu uma syscall
            kill(syscall_req.pid, SIGSTOP);
            printf("[Kernel] Recebeu syscall do PID %d (PC=%d).\n", syscall_req.pid, syscall_req.pc);

            
            for (int i = 0; i < NUM_PROCS_APP; i++) {
                if (process_table[i].pid == syscall_req.pid) { // Encontra o processo que fez a syscall
                    process_table[i].pc = syscall_req.pc;
                    process_table[i].state = BLOCKED;
                    process_table[i].blocked_on_device = syscall_req.device;
                    process_table[i].blocked_on_operation = syscall_req.operation;
                    
                    if (syscall_req.device == DEVICE_D1) blocked_queue_d1[d1_q_size++] = process_table[i].pid;
                    else blocked_queue_d2[d2_q_size++] = process_table[i].pid;
                    
                    printf("[Kernel] Processo A%d (PID %d) bloqueado esperando por %s.\n", i + 1, process_table[i].pid, device_to_str(syscall_req.device));
                    
                    int next_proc_idx = -1; 
                    for (int i = 1; i <= NUM_PROCS_APP; i++) { // Busca o próximo processo pronnto
                        int candidate_idx = (current_running_idx + i) % NUM_PROCS_APP; // busca circular pelo primeiro processo pronto após o que será interrompido
                        if (process_table[candidate_idx].state == READY) {
                            next_proc_idx = candidate_idx;
                            break;
                        }
                    }

                    if (next_proc_idx != -1) { // Encontrou um processo pronto
                        dequeue_ready();
                        current_running_idx = next_proc_idx;
                        process_table[current_running_idx].state = RUNNING;
                        kill(process_table[current_running_idx].pid, SIGCONT);
                        printf("[Kernel] Contexto trocado para o processo A%d (PID %d).\n", current_running_idx + 1, process_table[current_running_idx].pid);
                    } else {
                        current_running_idx = -1;
                        printf("[Kernel] Nenhum processo na fila de prontos para executar.\n");
                    }
                
                }
            }
        }
        
        for (int i = 0; i < NUM_PROCS_APP; i++) {
            printf("[Kernel] Total de iterações do processo A%d (PID %d): %d/%d", i + 1, process_table[i].pid, process_table[i].pc, MAX_ITERATIONS);
            printf(" Estado: %s\n", state_to_str(process_table[i].state));
            if (process_table[i].state != TERMINATED && process_table[i].pc >= MAX_ITERATIONS) {
                process_table[i].state = TERMINATED;
                printf("[Kernel] Processo A%d (PID %d) terminou sua execução.\n", i + 1, process_table[i].pid);
                all_processes_terminated++;
            }
        }

        if (all_processes_terminated == NUM_PROCS_APP) {
            break;
        }
    }
    
    printf("\n[Kernel] Todos os processos de aplicação terminaram. Encerrando o simulador.\n");
    kill(inter_controller_pid, SIGKILL);
    kill(kernel_pid, SIGKILL);
    exit(0);
}

// --- FUNÇÃO PRINCIPAL ---
int main() {
    if (pipe(irq_pipe) == -1 || pipe(syscall_pipe) == -1) {
        perror("Erro ao criar pipe");
        exit(EXIT_FAILURE);
    }
    // Tornar irq_pipe[0] não-bloqueante para podermos drenar sem bloquear
    int flags_irq = fcntl(irq_pipe[0], F_GETFL, 0);
    fcntl(irq_pipe[0], F_SETFL, flags_irq | O_NONBLOCK);
    int flags_syscall = fcntl(syscall_pipe[0], F_GETFL, 0);
    fcntl(syscall_pipe[0], F_SETFL, flags_syscall | O_NONBLOCK);

    if ((inter_controller_pid = fork()) == 0) {
        close(irq_pipe[0]); close(syscall_pipe[0]); close(syscall_pipe[1]);
        inter_controller_logic();
        exit(0);
    }

    if ((kernel_pid = fork()) == 0) {
        close(irq_pipe[1]);
        // Configura os handlers de sinal
        signal(SIGINT, sigint_handler);
        signal(SIGUSR1, sigusr1_handler);
        kernel_logic();
        exit(0);
    }

    close(irq_pipe[0]); close(irq_pipe[1]);
    close(syscall_pipe[0]); close(syscall_pipe[1]);

    printf("Simulador iniciado. PIDs:\n");
    printf("- KernelSim: %d\n", (int)kernel_pid);
    printf("- InterControllerSim: %d\n", (int)inter_controller_pid);
    printf("Para visualizar o estado, use o comando: kill -SIGINT %d\n", (int)kernel_pid);

    waitpid(kernel_pid, NULL, 0);
    kill(inter_controller_pid, SIGKILL);
    waitpid(inter_controller_pid, NULL, 0);

    printf("Simulador encerrado.\n");
    return 0;
}