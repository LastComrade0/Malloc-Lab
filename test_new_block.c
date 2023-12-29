#include <stdio.h>
#include <stdlib.h>

int addblock(int block){
        block = ((block + 1) >> 1) << 1;

        return block;
    }

int main(){

    int block = 5;

    block = ((block + 1) >> 1) << 1;

    printf("%d", block);


    return 0;
}