#include <sys/types.h>
#include <unistd.h>
#include <sys/stat.h>
#include <sys/mman.h>
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

int main(int argc, char ** argv){

    int numBytes = 0;
    int i;
    int fd = open("/dev/mem", O_RDWR | O_SYNC);

    unsigned * mem = (unsigned *)mmap(0, 1, PROT_READ | PROT_WRITE, MAP_SHARED, fd, 0xE0000000);

    for(;;){
        numBytes = *(mem+1);
        if(numBytes > 0 ){
            for(i = 0; i < numBytes; i++){
               printf("%02x", (char)*(mem+2));
            }
            close(fd);
            return 0;
        }
        //sleep(1);
    }

    return 0;
}
