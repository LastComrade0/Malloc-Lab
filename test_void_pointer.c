#include <stdio.h>
#include <stdlib.h>


int main(){
    
    
    void *ptr;

    int num = 1;

    ptr = &num;

    printf("Int ptr is %d.\n", (int)(ptr));


    return 0;
}