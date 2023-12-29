#include <stdio.h>
#include <stdlib.h>

typedef struct node Node_property;

int checker(int check){
    if(check){
        return 1;
    }
    else{
        return 0;
    }
}

typedef struct node{
    size_t data;
    Node_property *Next;
    Node_property *Prev;
}Node;

int main(int argc, char *argv[]){

    Node a, b, c;
    Node *ptr = &a;

    a.data = 10;
    a.Next = &b;
    a.Prev = NULL;

    b.data = 20;
    b.Next = &c;
    b.Prev = &a;

    c.data = 30;
    c.Next = NULL;
    c.Prev = &b;

    while(ptr != NULL){
        printf("\nAddress: %p, ", ptr); //Address
        printf("Data: %lu, ", ptr->data); //Data
        printf("Next Address: %p\n", ptr->Next);
        if(ptr->Next == NULL){
            break;
        }
        ptr = ptr->Next;
    }


    while(ptr != NULL){
        printf("\nAddress: %p, ", ptr); //Address
        printf("Data: %lu, ", ptr->data); //Data
        printf("Prev Address: %p\n", ptr->Prev);
        ptr = ptr->Prev;
    }

    printf("\n%lu\n", sizeof(Node));

    printf("Size of size_t is: %lu\n", sizeof(size_t));

    printf("%lu\n", (139637828775968 % 16));


    
    printf("\n%d\n", checker(1));
    





}
