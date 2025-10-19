#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <sys/wait.h>
#include <signal.h>
#include <time.h>
#include <string.h>
#include <errno.h> // Adicionado para o tratamento de erros
#include <fcntl.h>

int main(void){
    sleep(1);
    printf("Hello, World!\n");
    return 0;
}