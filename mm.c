/*
 * mm.c
 *
 * Name: Kejiang Zhang 939015486, YenHsiang Chen 959593906, Zhengjie Qian 972362832
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 * Also, read malloclab.pdf carefully and in its entirety before beginning.
 *
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <stdbool.h>
#include <stdint.h>

#include "mm.h"
#include "memlib.h"

/*
 * If you want to enable your debugging output and heap checker code,
 * uncomment the following line. Be sure not to have debugging enabled
 * in your final submission.
 */
//#define DEBUG

#ifdef DEBUG
/* When debugging is enabled, the underlying functions get called */
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_assert(...) assert(__VA_ARGS__)
#else
/* When debugging is disabled, no code gets generated */
#define dbg_printf(...)
#define dbg_assert(...)
#endif /* DEBUG */

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mem_memset
#define memcpy mem_memcpy
#endif /* DRIVER */



/*Global static variables*/

static void* memory_heap_start_pointer;

static void* freelist_start;

static  void* global_epilogue_address;

/* What is the correct alignment? */
#define ALIGNMENT 16

/* Custom Defines */

#define HEADER_SIZE 8
#define FOOTER_SIZE 8
#define MINIMUM_ALIGNMENT 16
#define WORD_SIZE 8 //Since 64 bit machine, word size is 8 byte
#define PROLOGUE_SIZE 16 //16 bytes of prologue
#define EPILOGUE_SIZE 8 //8  bytes of epilogue
#define Allocate_Block 1
#define Free_Block 0
#define Free_List_Number 11
#define Free_List_Size 176






/* rounds up to the nearest multiple of ALIGNMENT */
static size_t align(size_t x)
{   
    size_t aligned;

    if(x <= MINIMUM_ALIGNMENT){
        aligned = MINIMUM_ALIGNMENT + MINIMUM_ALIGNMENT;
        return aligned;
    }

    else{
        return ALIGNMENT * ((x+ALIGNMENT-1)/ALIGNMENT);
    }
    
}




/*-------------------------------------------------------------------------------------------------------*/

/* Structs */



//Size of header and footer's
typedef struct {

    size_t size;

}Header_Footer;


//Prologue block struct
typedef struct {
    
    size_t Padding;
    Header_Footer Header; //Header of prologue block
    Header_Footer Footer; //Footer of prologue block

}Prologue_Block;


//Epilogue block struct
typedef struct {
    Header_Footer Header; //No need Footer as boundary in end of heap
}Epilogue_Block;


//Free list struct
typedef struct Linked_List{
    struct Linked_List *prev;
    struct Linked_List *next;
} Free_List;

/*-------------------------------------------------------------------------------------------------------*/

/* Function Prototypes*/
static void set_prologue_epilogue_header(Header_Footer* header, size_t block_size, int allocation_status);

static void set_prologue_epilogue_footer(Header_Footer* footer, size_t block_size, int allocation_status);

static void set_header(Header_Footer* header, size_t block_size, int allocation_status);

static void set_footer(Header_Footer* footer, size_t block_size, int allocation_status);

static void set_prologue_block(Prologue_Block* prologue_block);

static void set_previous_allocation_status(Header_Footer* header, size_t get_allocation_status);

static size_t get_previous_allocation_status(Header_Footer* header);

static void initialize_free_list(Free_List* ptr);

static bool is_end_of_list(Free_List* list_head_pointer, Free_List* next_pointer);

static size_t get_size(Header_Footer* header_or_footer);

static size_t get_allocation_status(Header_Footer* header_footer);

static void* check_block(Free_List* list_head_pointer, size_t size);

static void* increase_heap(size_t size_needed);

static void* find_free(size_t payload);

static void* find_fit(void* header_pointer, size_t aligned_total_size);

static void add_free_node(Free_List* head_pointer, Free_List* list_node_pointer);

static void delete_free_node(Free_List* list_node_pointer);

static void coalesce_free_block(void* pointer);



/* ------------------------------------------------------------------------------------------------------*/ 


/* Helper Functions */

//Set header and footers for prologue and epilogue blocks
static void set_prologue_epilogue_header(Header_Footer* header, size_t block_size, int allocation_status){
    header->size = (header->size & 3) | block_size ; /*Mask out every bit except allocation status bit and
                                                        previous allocation status bit. Then contacnate 
                                                        the masked bits with block size.*/
                                                        

    header->size = (header->size & -2) | Allocate_Block; /*Mask out the last bit whether it is 0 or 1.
                                                            Then contacnate 1 to last bit since prologue
                                                            and epilogue should be marked as allocated.*/

    /* Only epilogue will have size 0, so prologue will set second last bit of next block's allocation
    status to state this block is allocated.*/
    if(block_size != 0){
        set_previous_allocation_status( (void*)  ( (char*)header + get_size(header)), (allocation_status << 1));
    }
    
};


//Set the footer for prologue and epilogue
static void set_prologue_epilogue_footer(Header_Footer* footer, size_t block_size, int allocation_status){
    footer->size = block_size; //Set blocksize to footer
};





//Set Header
static void set_header(Header_Footer* header, size_t block_size, int allocation_status){
    header->size = (header->size & 3) | block_size ; /*Mask out every bit except allocation status bit and
                                                        previous allocation status bit. Then contacnate 
                                                        the masked bits with block size.*/

    header->size = (header->size & -2) | allocation_status; /*Mask out the last bit whether it is 0 or 1.
                                                            Then contacnate the allocations to last bit.                                                            and epilogue should be marked as allocated.*/


    /* Since every blocks will have size value other than 0, so will set second last bit of next 
    block's allocationstatus to state that this block is being allocated. The only exception is if 
    the next block is epilogue, then the condition statement will not execute*/
    if(block_size != 0){
        set_previous_allocation_status( (void*)  ( (char*)header + get_size(header)), (allocation_status << 1));
    }
    
};

//Set Footer
static void set_footer(Header_Footer* footer, size_t block_size, int allocation_status){
    footer->size = block_size; //Set blocksize to footer
};



//Set prologue block
static void set_prologue_block(Prologue_Block* prologue_block){
    set_prologue_epilogue_header(&(prologue_block->Header), PROLOGUE_SIZE, Allocate_Block);

    set_prologue_epilogue_footer(&(prologue_block->Footer), PROLOGUE_SIZE, Allocate_Block);
};


/*Set previous allocation status to the next block if the next block is not epilogue(size is 0), 
when next block is visited, the 2nd bit can tell if previous block is free or allocated without
looking footer.*/
static void set_previous_allocation_status(Header_Footer* header, size_t allocation_status){

    /*Mask out every bit except 2nd last bit. Then set allocation status to 2nd last bit as previous 
    allocation indicator*/
    header->size = (header->size & -3) | allocation_status; 

}


//Get allocation status from previous block
static size_t get_previous_allocation_status(Header_Footer* header){

    /*Mask out every bit except 2nd last bit, then push bit to right by 1 to see if previous block's
    allocation status is 0 or 1*/
    return (header->size & 2) >> 1;  

}



//List initialization
static void initialize_free_list(Free_List* ptr){
    ptr->next = ptr; //Initialize free block pointer's next free block pointer as itself
    ptr->prev = ptr; //Initialize free block pointer's previous free block pointer as itself
}



static void* search_list_num(size_t input_size){

    char list_num; //Variable of which list number to return

    if(input_size <= 32) {list_num = 0;} //Set list number 0 to return if desired free block size is <= 32

    else if(input_size <= 64) {list_num = 1;} //Set list number 1 to return if desired free block size is <= 64

    else if(input_size <= 128) {list_num = 2;} //Set list number 2 to return if desired free block size is <= 128

    else if(input_size <= 256) {list_num = 3;} //Set list number 3 to return if desired free block size is <= 256

    else if(input_size <= 512) {list_num = 4;} //Set list number 4 to return if desired free block size is <= 512

    else if(input_size <= 1024) {list_num = 5;} //Set list number 5 to return if desired free block size is <= 1024

    else if(input_size <= 2048) {list_num = 6;} //Set list number 6 to return if desired free block size is <= 2048

    else if(input_size <= 4096) {list_num = 7;} //Set list number 7 to return if desired free block size is <= 4096

    else if(input_size <= 8192) {list_num = 8;} //Set list number 8 to return if desired free block size is <= 8192

    else if(input_size <= 16384) {list_num = 9;} //Set list number 9 to return if desired free block size is <= 16384

    else {list_num = 10;} //Set list number 10 to return if desired free block size is larger than 16384

    return freelist_start + (list_num * 16); //Return correct address to start searching in the correct list

}

/*Boolean function to tell if the current free block pointer reaches the end of the current free list.*/
static bool is_end_of_list(Free_List* list_head_pointer, Free_List* next_pointer){

    if(list_head_pointer == next_pointer){
        return true;
    }

    else{
        return false;
    }



}

//Get the size of block
static size_t get_size(Header_Footer* header_or_footer){

    size_t block_size = header_or_footer->size & -16; /*Mask out last 4 bits to get block size.
                                                        Since block size will only be multiple of
                                                        16, so no need to worry about last 4 bits*/
    return block_size; 

}



//Get allocation status of the block
static size_t get_allocation_status(Header_Footer* header_footer){
    return header_footer->size & 1; //Mast out every bit except last bit to get allocation status
}




//Check through list if there is satisfactory block existing
static void* check_block(Free_List* list_head_pointer, size_t size){

    Free_List *select_pointer = list_head_pointer->next; //Set the pointer to the 1st free block of list(pointer straight next to head pointer of free list)

    Free_List* last_list_header = freelist_start + ((Free_List_Number-1)*sizeof(Free_List)); //Set the last header pointer for the whole free list(end of free list)

    while (true){

        /*Iterate through the list until reaches end of local list. If nothing is fount in 
        local list, go search the larger list.*/
        while(is_end_of_list(list_head_pointer, select_pointer)){
            if(list_head_pointer == last_list_header){
                return NULL;
            }

            list_head_pointer += 1; //Increment the list's head pointer, meaning to search in next larger index list

            select_pointer = list_head_pointer->next; //Set the pointer to the 1st free block of the list

        }

         /*Important to typecast char* for select_pointer, otherwise move left by wordsize will cause 
         moving left by 16 instead of 8*/
        if(get_size((void* )(((char*)(select_pointer)) - WORD_SIZE)) >= size){
            return select_pointer;
        }

        //Go to the next node of free block in linked list
        select_pointer = select_pointer->next;

    }

    //return select_pointer;
    
}

//Expand heap, apply new size
static void* increase_heap(size_t size_needed){

    //Set variable of payload  pointer
    void* payload_pointer = NULL;

    void* new_pointer = mem_sbrk(size_needed);//Get the pointer after calling increase heap function

    void* new_head_pointer = NULL; //Set variable for new head pointer

    //If mem_sbrk() returns pointer and recorded to new pointer
    if(new_pointer != NULL){ 
        payload_pointer = new_pointer;// Copy the new_pointer to payload pointer
        //printf("%p", payload_pointer);
    }
    else{
        return NULL; //If mem_sbrk() returned -1, fail.
    }

    //Create new header

    new_head_pointer = (void*)((char*)(new_pointer - WORD_SIZE)); //Move toward 8 byts for header pointer

    set_header(new_head_pointer, size_needed, Allocate_Block); //Set new header


    //Set New Epilogue
    Epilogue_Block* epilogue_address = (void*)(((char*)(new_pointer)-8)+get_size(new_head_pointer)); //Set new Epilogue address

    set_prologue_epilogue_header(&(epilogue_address->Header), 0 , Allocate_Block);//Set Epilogue Header

    global_epilogue_address = epilogue_address;//Update to global epilogue address for recording use

    return payload_pointer;

    

}



//Look for existing free block in malloc() and realloc()
static void* find_free(size_t payload){

    size_t aligned_total_size = align(payload + HEADER_SIZE); //Set the size aligned to 16 bytes

    void* list_head_pointer = search_list_num(aligned_total_size); //Determine which list to initiae the search based on size

    void* select_pointer = check_block(list_head_pointer, aligned_total_size); /*Select payload pointer comes after searching
                                                                                throughout the list, if found free block, return
                                                                                the free block pointer. Else, return NULL.*/


    //If no satisfactory freed block found, increase the heap
    if(select_pointer == NULL){

        return increase_heap(aligned_total_size); 

    } else {//Find fitting free block

        return find_fit(select_pointer - WORD_SIZE, aligned_total_size); //Move payload pointer to header pointer and fit in the free block
    }



    return NULL;

    
}

/*Fit in a free block if find. After fit, if unused block is larger than 32 bytes
(Header(8 Bytes)) + Footer(8 Bytes) + atleast a block(16 Bytes))*/
static void* find_fit(void* header_pointer, size_t aligned_total_size){
    size_t empty_space = get_size(header_pointer) - aligned_total_size; /*The empty space will occur when free block
                                                                        subtracts the desired allocating aligned size.*/

    if(empty_space >= (MINIMUM_ALIGNMENT*2)){//If empty space is larger than the size of Header and footer and at least 1 payload block which is total 32 bytes
        
        //Get the free block's footer pointer
        void* footer_pointer = (header_pointer + get_size(header_pointer) - WORD_SIZE);

        //If the block is free status
        if(get_allocation_status(header_pointer) == Free_Block){
            delete_free_node(header_pointer + WORD_SIZE); //Delete current free block from free list
        }
        set_header(header_pointer, aligned_total_size, Allocate_Block); //Set the free block to allocated status




        void* new_free_header = header_pointer + get_size(header_pointer); /*Declare new free block header pointer which
                                                                            starts from the previously created allocated
                                                                            block pointer + size of block. This means 
                                                                            splitted.*/

        set_header(new_free_header, empty_space, Free_Block); //Set splitted free block header

        //Check if the next of recently created free block's next block is also free
        if(get_allocation_status(new_free_header + get_size(new_free_header)) == Free_Block){

            //If next block is also free, coalesce them.
            coalesce_free_block(header_pointer + get_size(header_pointer));
        }

        //If no coalescing is needed
        else{
            set_footer(footer_pointer, empty_space, Free_Block); //Set footer for recently created/splitted free block

            //Add this recently created/splitted free block to linked list
            add_free_node(search_list_num(empty_space), ((header_pointer + get_size(header_pointer)) + WORD_SIZE));
        }

        return header_pointer + WORD_SIZE; //Return payload pointer


    }

    //If empty space is smaller than size of header + footer + 1 minimum payload block size
    else{
        if(get_allocation_status(header_pointer) == Free_Block){
            delete_free_node(header_pointer + WORD_SIZE); //Delete free block
        }
        set_header(header_pointer, get_size(header_pointer), Allocate_Block); //Set the header as allocated status

        return header_pointer + WORD_SIZE; //Return payload pointer
    }

    
}

//Add free block to free list
static void add_free_node(Free_List* head_pointer, Free_List* list_node_pointer){

    Free_List* next_pointer = head_pointer->next; //Record next pointer

    //Free_List* previous_pointer = head_pointer->prev;

    head_pointer->next = list_node_pointer; //Link new node to head_pointer

    list_node_pointer->next = next_pointer; //Link next pointer node to list node pointer

    next_pointer->prev = list_node_pointer; //Link the previous of nextpointer to list node pointer

    list_node_pointer -> prev = head_pointer; //set list node pointer's previous to head pointer


}

//Delete free node
static void delete_free_node(Free_List* list_node_pointer){

    list_node_pointer->next->prev = list_node_pointer->prev; //Unlink this node as set next node's previous as current previous

    list_node_pointer->prev->next = list_node_pointer->next; //Unlink this node as set previous node's next node as current next

}

//Coalesce free block
static void coalesce_free_block(void* header_pointer){
    size_t final_size = get_size(header_pointer); //Set the size first

    void* next_header = header_pointer + final_size; //Set the next header pointer of the current header

    void* payload_pointer = header_pointer + WORD_SIZE; //Set the payload pointerof current header

    //Case if the next block of this free block is free but previous is allocated
    if(get_allocation_status(next_header) == Free_Block && get_previous_allocation_status(header_pointer) == Allocate_Block){
        final_size += get_size(next_header); //Add the next block free size to current free block size

        delete_free_node(next_header + WORD_SIZE); //Delete next free block's data from linked list

        set_header(header_pointer, final_size, Free_Block); //Set new header for coalesced free block free with combined size

        set_footer((header_pointer + final_size - WORD_SIZE), final_size, Free_Block); //Set new footer for coalisced free block free with combined size

        add_free_node(search_list_num(final_size), payload_pointer); //Add the new coalesced free block to correct size label of free list


    }

    //Case if the next block of this free block is allocated but previous is free
    else if(get_allocation_status(next_header) == Allocate_Block && get_previous_allocation_status(header_pointer) == Free_Block){
        /*get previous block's header pointer by extracting size from previous block's free block footer,
        then locate the pointer by subtracting extracted size.*/
        void* previous_block_header_pointer = (header_pointer - WORD_SIZE) - get_size((header_pointer - WORD_SIZE)) + WORD_SIZE; //Go previous block head pointer by knowing size from previous footer

        final_size += get_size(previous_block_header_pointer); //Add the previous free block's size to current free block size

        delete_free_node(previous_block_header_pointer + WORD_SIZE); //Delete previous free block's data from free list

        set_header(previous_block_header_pointer, final_size, Free_Block); //Set new coalesced header starting from previous free block pointer with combined size

        set_footer((previous_block_header_pointer + final_size - WORD_SIZE), final_size, Free_Block); //Set new coalesced free block's footer with combined size

        add_free_node(search_list_num(final_size), (previous_block_header_pointer + WORD_SIZE)); //Add new coalesced free block to correct size label of free list



    }

    //Case if both previous and next free block are free
    else if(get_allocation_status(next_header) == Free_Block && get_previous_allocation_status(header_pointer) == Free_Block){
        //Get previous block head pointer by extracting size from footer. Then do pointer arithmetic.
        void* previous_block_header_pointer = (header_pointer - WORD_SIZE) - get_size((header_pointer - WORD_SIZE)) + WORD_SIZE; //Go previous block head pointer by knowing size from previous footer

        final_size += (get_size(next_header) + get_size(previous_block_header_pointer)); //Add up both previous and next free block's size

        delete_free_node(next_header + WORD_SIZE); //Delete next free block's data from free list

        delete_free_node(previous_block_header_pointer + WORD_SIZE); //Delete previous free block's data from free list

        set_header(previous_block_header_pointer, final_size, Free_Block); //Set new coalesced free block starting from previous block's header with combined size

        set_footer((previous_block_header_pointer+ final_size - WORD_SIZE), final_size, Free_Block); //Set new coalesced free block's footer with combined size

        add_free_node(search_list_num(final_size), (previous_block_header_pointer + WORD_SIZE)); //Add new coalesced free block to correct size label of free list

        
    }

    //If non of the previous 3 statements is satisfied
    else{

        return; 
    }
}



/*-----------------------------------------------------------------------------------------------------*/

/*
 * Initialize: returns false on error, true on success.
 */
bool mm_init(void)
{
    /* IMPLEMENT THIS */

    //Prologue(Header/Footer) + epilogue(Headeer) + blank block alignment(to compensate epilogue header only has 8 bytes) + (list size(8 byte) * 11)
    size_t set_size = align((4 * WORD_SIZE) + ((sizeof(Free_List)) * 11)); 

    freelist_start = mem_sbrk(set_size); //Call 208 bytes aka 13 blocks or 26 blocks and set the very first address as start pointer

    /*Initialize double linked Free List*/

    memory_heap_start_pointer = freelist_start; //Set the starting address of freelist as very first address

    for(char i =  0; i < Free_List_Number; i+=1){

        initialize_free_list((void*) ((char*)(freelist_start) + i*sizeof(Free_List))); //Initialize 11 free lists

    }


    /* Set Prologue*/
    Prologue_Block* prologue_address = memory_heap_start_pointer + (Free_List_Size); //Memory Heap Start Pointer + Size of Free List

    set_prologue_epilogue_header(&(prologue_address->Header), PROLOGUE_SIZE, Allocate_Block); //Set header

    set_prologue_epilogue_footer(&(prologue_address->Footer), PROLOGUE_SIZE, Allocate_Block); //Set footer

    /* Set Epilogue*/
    Epilogue_Block* epilogue_address = (void*)(((char*)(memory_heap_start_pointer)) + 8 + Free_List_Size + EPILOGUE_SIZE + 8);// Prologue address + Prologue Footer + Epilogue_Size + Blank padding

    set_prologue_epilogue_header(&(epilogue_address->Header), 0, Allocate_Block); //Set epilogue header


    /* Set the start of the memory allocation in the position of Epilogue*/
    memory_heap_start_pointer = epilogue_address;

    mm_checkheap(__LINE__);

    return true;
}

/*
 * malloc
 */
void* malloc(size_t size)
{
    
    //Return NULL if no payload
    if(size == 0){
        return NULL;
    }

    //Find free block to allocate. If not, the heap will be expanded.
    void* pointer = find_free(size); 

    //Filler function call to look at epilogue's previous block's allocation status.
    get_previous_allocation_status(global_epilogue_address); 
    
    mm_checkheap(__LINE__);

    return pointer; //Returns payload pointer
}

/*
 * free
 */
void free(void* ptr)
{   
    /* IMPLEMENT THIS */
    if(ptr == NULL){
        return;
    }


    void* header_pointer = (ptr - WORD_SIZE); //-8 byte to locate header
    
    size_t header_pointer_size = get_size(header_pointer); //Size of block got from header
    
    void* next_header_pointer = (ptr + header_pointer_size);  //Next block's header pointer

    //size_t next_header_pointer_size = get_size(next_header_pointer); //Next block's size

    size_t previous_header_allocation = get_previous_allocation_status(header_pointer); //Get previous block's allocation status by 2nd byte due to no footer in this program

    //Case if either previous or next block's allcoation status is free, coalesce it.
    if(get_allocation_status(next_header_pointer - WORD_SIZE) == Free_Block || previous_header_allocation == Free_Block){
        coalesce_free_block(header_pointer);
    }

    //Case if none of the block adjacent to this current block are free 
    else{
        set_header(header_pointer, header_pointer_size, Free_Block); //Set header from allocated to free

        void* footer_pointer = header_pointer + header_pointer_size - HEADER_SIZE; //Set footer pointer according to the size

        set_footer(footer_pointer, header_pointer_size, Free_Block); //Set new footer pointer for this block due to this is free block

        void* payload_pointer = ptr; 

        add_free_node(search_list_num(header_pointer_size), payload_pointer); //Add created free block to free list
    }

    //Filler function call to check epilogue information
    get_previous_allocation_status(global_epilogue_address);

    mm_checkheap(__LINE__);

    return; //Return nothing
}

/*
 * realloc
 */
void* realloc(void* oldptr, size_t size)
{
    /* IMPLEMENT THIS */
    size = align(size + WORD_SIZE); //Align block + header size

    //If old pointer is NULL, just malloc
    if(oldptr == NULL){
        malloc(size);
    }

    //If size is 0, treat it as free
    if(size == 0){
        free(oldptr);

        return NULL;
    }

    //
    void* old_pointer_header = oldptr - WORD_SIZE; //Move to header of old block

    //If the old block's size is larger than size input
    if(get_size(old_pointer_header) >= size){
        find_fit(old_pointer_header, size); //Find fit of the old block

        mm_checkheap(__LINE__);

        return oldptr; //Return old pointer
    }

    //Find new block if input size is larger than old block's size, find a new block, same as malloc
    old_pointer_header = find_free(size); 

    //Compare sizes
    //Size 1 is the size of old block
    size_t compare_size_1 = get_size((oldptr - WORD_SIZE)) -  WORD_SIZE;

    //Size 2 is the size of new block
    size_t compare_size_2 = size;

    //Variable for final comparison of which is the min size
    size_t final_comparison;
    
    //If size of old block is smaller than new block, return old block size
    if(compare_size_1 <= compare_size_2){
        final_comparison = compare_size_1;
    }
    //Else the min size is new block size
    else{
        final_comparison = compare_size_2;
    }

    mem_memcpy(old_pointer_header, oldptr, final_comparison); //Copy the content to new block

    free(oldptr); //Free old block

    mm_checkheap(__LINE__);

    return old_pointer_header; //Return the header pointer
    
}

/*
 * calloc
 * This function is not tested by mdriver, and has been implemented for you.
 */
void* calloc(size_t nmemb, size_t size)
{
    void* ptr;
    size *= nmemb;
    ptr = malloc(size);
    if (ptr) {
        memset(ptr, 0, size);
    }
    return ptr;
}

/*
 * Returns whether the pointer is in the heap.
 * May be useful for debugging.
 */
static bool in_heap(const void* p)
{
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}

/*
 * Returns whether the pointer is aligned.
 * May be useful for debugging.
 */
static bool aligned(const void* p)
{
    size_t ip = (size_t) p;
    return align(ip) == ip;
}

/*----------------------------------------------------------------------------------------------------*/

/*
 * mm_checkheap
 */


                        /*General check for both allocated and free blocks*/

//Check if pointer is in heap boundary
static bool is_in_heap(const void* pointer){
    if(pointer >= mem_heap_lo() && pointer <= mem_heap_hi()){
        return true;
    }

    else{
        return false;
    }
}

//Check if block is aligned to 16 bytes
static bool is_aligned(const void* pointer){
    size_t proof_pointer = (size_t) (pointer);

    if(align(proof_pointer) == proof_pointer){
        return true;
    }

    else{
        return false;
    }
}

//Check if previous allocation status does not match to current allocation status
static bool current_and_previous_match(Header_Footer* header_pointer){
    
    if(get_size(header_pointer) != 0){// Only epilogue has no size
        Header_Footer* next_head_pointer = (void*)((char*)header_pointer) + get_size(header_pointer); //Get next block's pointer

        size_t current_allocation_status = get_allocation_status(header_pointer); //Get current block's allocation status

        size_t previous_allocation_status = get_previous_allocation_status(next_head_pointer);  //Get previous block's allocation status

        //Check if previous and current allocation status matches
        if(current_allocation_status == previous_allocation_status){
            return true;
        }

        else{
            return false;
        }

    }

    else{

        //Case if is epilogue
        return  true;
    }


}

                                /*Only check for free block*/

//Check if the header and footer of free block is identical
static bool identical_header_footer(Header_Footer* free_header_pointer){

    //Get footer of free block
    Header_Footer* free_footer_pointer = (void*)((char*)free_header_pointer) + get_size(free_header_pointer) - WORD_SIZE;

    
    if(get_size(free_header_pointer) == get_size(free_footer_pointer)){
        return true;
    }

    else{
        return false;
    }


}


//Check if every free block is in the free list
static bool included_in_free_list(Header_Footer* free_block_header){
    size_t free_block_size  = get_size(free_block_header); //Get size of freeblock

    Free_List* list_head = search_list_num(free_block_size); //Get the correct list starting header by size

    Free_List* node_pointer = (void*) (((char*)free_block_header) + WORD_SIZE); //Get the pointer to be checked

    Free_List* select_pointer = list_head->next; //Move node  pointerbe checked to first node

    //Iterate through the current list until end
    while(!is_end_of_list(list_head,select_pointer)){
        
        //If the select_pointer iteration matches the target node pointer, then free block is found in free list
        if(select_pointer == node_pointer){

            return true;

        }

        //If no match, go to next pointer of select pointer then loop while again
        select_pointer = select_pointer->next;


    }

    return false;


}



bool mm_checkheap(int lineno)
{
#ifdef DEBUG
    /* Write code to check heap invariants here */

    /*Some pointer variables*/

    void* header_pointer = memory_heap_start_pointer; //Start checking from the start of heap

    bool contiguous = false; //Control status to indicate if free blocks are contiguous

    void* previous_payload_start = NULL; //Payload start of previous block

    void* previous_payload_finish = NULL; //Payload end of previous block

    void* payload_start = NULL; //Payload start of current block

    void* payload_finish = NULL; //Payload end of current block

    bool searching = true; //Loop control of searching

    //Traverse through entire heap until epilogue
    while(searching == true){

        //Check if the block is in heap
        if(is_in_heap(header_pointer) == false){
            dbg_printf("Block is not in heap.\n");

            return false;
        };

        //Check if the block is aligned to 16 bytes
        if(is_aligned(header_pointer + WORD_SIZE) == false){
            dbg_printf("Block: %p is not aligned in 16 bytes.", header_pointer  + WORD_SIZE);

            return false;
        }

        //Check if both current block allocation staus matches to next block's previous allocation status.
        if(current_and_previous_match(header_pointer) == false){
            dbg_printf("Current allocation status is different than nex block's previous allocation status.\n");

            return false;
        }


        /*Case if the pointer allocation status is FREE*/

        //Counter of contiguous 
        static int contiguous_count;

        if(get_allocation_status(header_pointer) == Free_Block){
 

            contiguous_count += 1; //Increment contiguous by default

            if (contiguous_count > 1){
                contiguous = true; //Boolean of finding contiguous free blocks
            }

            if(contiguous == true){
                
                dbg_printf("Contiguous free blocks exist.\n"); //Return error if fount contiguous free blocks

                return false;
            }

            //Check if both header and footer of free block are identical
            if (identical_header_footer(header_pointer) == false){

                dbg_printf("Header and footer of free block: %p does not match.\n",header_pointer);

                return false;
            }

            //Check if the free block is in free list
            if(included_in_free_list(header_pointer) == false){
                
                dbg_printf("Freeblock: %p is not in Free lest.\n", (header_pointer + WORD_SIZE));

                return false;
            }

            //When all check list for free block is finished
            else{
                contiguous_count = 0; //Reset contiguous count to indicate there is no contiguous  free blocks

                //Check payload overlapping
                payload_start = header_pointer + WORD_SIZE; //Payload start of block

                payload_finish = header_pointer + get_size(header_pointer); //Payload end of block

                if(payload_start < previous_payload_finish){
                    //Error if payload overlaps
                    dbg_printf("Payload: %p to %p overlaps with previous payload: %p to %p", payload_start, payload_finish, previous_payload_start, previous_payload_finish);

                    return false;
                }

                else{

                    //Make current payload to previous one for next check
                    previous_payload_start = payload_start;

                    previous_payload_finish = payload_finish;

                }


            }

        }




        //Finished checking current block

        //If the size is 0, means epilogue is reached, then stop the check
        if(get_size(header_pointer) == 0){
            //dbg_printf("Heap check passed!\n");
            break;
        }

        //If epilogue is not reached, move to next block pointer and loop the check again
        else{
            header_pointer = (void*)((char* )header_pointer) + get_size(header_pointer);
        }
    }



    /* IMPLEMENT THIS */
#endif /* DEBUG */
    //printf("True");
    return true; //When everything is alright, return true for check heap
}

