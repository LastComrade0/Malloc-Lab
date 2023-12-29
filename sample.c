/*

 * mm.c               

 */

#include <assert.h>

#include <stdlib.h>

#include <stdio.h>

#include <string.h>

#include <unistd.h>

#include <stdint.h>

#include <stdbool.h>



#include "mm.h"

#include "memlib.h"



/*

 * If you want to enable your debugging output and heap checker code,

 * uncomment the following line. Be sure not to have debugging enabled

 * in your final submission.

 */

//#define DEBUG



#ifdef DEBUG

// When debugging is enabled, the underlying functions get called

#define dbg_printf(...) printf(__VA_ARGS__)

#define dbg_assert(...) assert(__VA_ARGS__)

#else

// When debugging is disabled, no code gets generated

#define dbg_printf(...)

#define dbg_assert(...)

#endif // DEBUG



// do not change the following!

#ifdef DRIVER

// create aliases for driver tests

#define malloc mm_malloc

#define free mm_free

#define realloc mm_realloc

#define calloc mm_calloc

#define memset mm_memset

#define memcpy mm_memcpy

#endif // DRIVER



#define ALIGNMENT 16

#define HDFT_SIZE 8

#define PROLOGUE_SIZE 16

#define EPILOGUE_SIZE 8

#define MINBLOCKSIZE 32

#define SIZE32 32

#define SIZE64 64

#define SIZE128 128

#define SIZ256 256

#define SIZE512 512

#define SIZE1024 1024

#define SIZE2048 2048

#define SIZE4096 4096

#define SIZE8192 8192

#define SIZE16384 16384

#define FREELISTNUM 11

#define ALLOC 1

#define FREE 0



enum ptrMove {

    hdcurr_to_pld,     //from current header to payload 

    hdcurr_to_ftcurr, //from current header to footer 

    hdcurr_to_hdnext, //from current header to next header 

    hdcurr_to_ftprev, //from current header to previous footer

    ftcurr_to_hdcurr,  //from footer to current header

    pld_to_hdcurr,     //from first to current header 

    pad_to_hdcurr      //from padding to current header 

};



//////////////////////////////////////////////////

// Data structures Defination

////////////////////////////////////////////////// 

// #1 Hdft: Stucture for header and footer, since they both have only one member size. 

typedef struct {

    size_t size;

} Hdft;



// #2 Prologue: The start of the heap, include a header and a footer 

typedef struct {

    size_t padding;

    Hdft header;

    Hdft footer;

} Prologue;



// #3 Epilogue: The end of the heap, include a header

typedef struct {

    Hdft header;

} Epilogue;



// #4 LinkedListNode: explict linked noted used to store free block info

typedef struct LinkedListNode {

    struct LinkedListNode* next;

    struct LinkedListNode* prev;

} FreeList;



//////////////////////////////////////////////////

// Static var

////////////////////////////////////////////////// 

static void* heap_start;

static void* freelist_start;



//////////////////////////////////////////////////

// function declear

////////////////////////////////////////////////// 

static size_t align(size_t x);

static void* pointer_move(void* ptr, enum ptrMove opt);

static void* size_switch(size_t size);

static void set_header(Hdft* header, size_t blk_size, int alloc_info);

static void set_footer(Hdft* footer, size_t blk_size, int alloc_info);

static void set_prev_alloc_info(Hdft* header, size_t prev_alloc_info);

static void set_prologue(Prologue* prologue);

static void set_epilogue(Epilogue* epilogue);

static size_t get_size(Hdft* hdft);

static size_t get_alloc(Hdft* hdft);

static size_t get_prev_alloc(Hdft* hdft);

static void list_init(FreeList* head);

static void node_add(FreeList* hd_ptr, FreeList* nd_ptr);

static void node_del(FreeList* nd_ptr);

static bool at_list_end(FreeList* hd_ptr, FreeList* nd_ptr);

static void* find_block(size_t payload_size);

static void* check_size(FreeList* list_hd_ptr, size_t size);

static void* fitin_block(void* hd_ptr, size_t size_needed);

static void* heap_exp(size_t size_needed);

static void coalesce_block(void* hd_ptr);

static size_t min(size_t size1, size_t size2);



//////////////////////////////////////////////////

// Helper functions

////////////////////////////////////////////////// 

/* align: rounds up to the nearest multiple of ALIGNMENT.

 * input: requested size 

 * output: size rounded up to  the nearest multiple of ALIGNMENT

 */

static size_t align(size_t x)

{

    size_t aligned_size =  ALIGNMENT * ((x+ALIGNMENT-1)/ALIGNMENT);

    // As the align is 16 but min block is 32, we have to upround 16size block to 32

    if(aligned_size < MINBLOCKSIZE){

        aligned_size = MINBLOCKSIZE;

    }

    return aligned_size;

}



/* pointer_move: move the pointer 

 * input: (1)pointer to move (2) which kind of option  

 * output: pointer after move

 */

static void* pointer_move(void* ptr, enum ptrMove opt)

{

    size_t size = 0;

    switch (opt){           

    case hdcurr_to_pld: //from current header to payload 

        return (void *)((char *)(ptr) + HDFT_SIZE); //move header size, right 

    case hdcurr_to_ftcurr: //from current header to cur footer

        size = get_size(ptr); //get block size

        return (void *)((char *)(ptr) + size - HDFT_SIZE);  //move block size, right, then move footer size left  

    case hdcurr_to_hdnext: //from current header to next header 

        size = get_size(ptr); //get block size

        return (void *)((char *)(ptr) + size); //move block size, right    

    case hdcurr_to_ftprev: //from current header to prev footer

        return (void *)((char *)(ptr) - HDFT_SIZE); //move footer size, left

    case ftcurr_to_hdcurr: // from current footer to cur header

        size = get_size(ptr); //get block size

        return (void *)((char *)(ptr) + HDFT_SIZE - size); //move move footer size right, then block size, right    

    case pld_to_hdcurr: //from payload to cur head 

        return (void *)((char *)(ptr) - HDFT_SIZE); //move header size, left

    case pad_to_hdcurr: //from padding to cur head 

        return (void *)((char *)(ptr) + sizeof(size_t)); //move padding size, right   

    default:

        return NULL;

    }

}



/* size_switch: decide which list to use according to the size request

 * input: size request(after round up)

 * output: list head

 */

static void* size_switch(size_t size){

    char i;

    if (size <= SIZE32)          i=0; 

    else if (size <= SIZE64)     i=1;

    else if (size <= SIZE128)    i=2;

    else if (size <= SIZ256)     i=3;

    else if (size <= SIZE512)    i=4;

    else if (size <= SIZE1024)   i=5;

    else if (size <= SIZE2048)   i=6;

    else if (size <= SIZE4096)   i=7;

    else if (size <= SIZE8192)   i=8;

    else if (size <= SIZE16384)  i=9;

    else  i=10;

    //compute the head addr of conreponding free list (baseaddr + offset)

    return freelist_start + (i * sizeof(FreeList));

}



/* set_header: store the size of the block and alloc info into the header

 * input: (1) addr of the header (2) size of the block(after round up) (3) free or alloc

 * output: void

 */

static void set_header(Hdft* header, size_t blk_size, int alloc_info)

{

    // (1) assign size of the block to header.size

    header->size = (header->size & 0x3) | blk_size; //  (header->size & 0x2) could protect prev alloc info 

    // (2) assign alloc info to the last bit of size

    header->size = (header->size & ~0x1) | alloc_info;

    if(blk_size){ // if cur block is not epi, set prev_alloc info to the next header

        set_prev_alloc_info(pointer_move(header, hdcurr_to_hdnext), (alloc_info << 1));

    }

}



/* set_footer: store the size of the block and alloc info into the footer

 * input: (1) addr of the footer (2) size of the block(after round up) (3) free or alloc

 * output: void

 */

static void set_footer(Hdft* footer, size_t blk_size, int alloc_info)

{

    // (1) assign size of the block to header.size

    footer->size = blk_size;

}



/* set_prologue: create a prologue contains a header and a footer

 * input: start addr 

 * output: void

 */

static void set_prologue(Prologue* prologue)

{

    // (1) set prologe header - size: HEADER_SIZE+FOOTER_SIZE, alloc_info: alloc

    set_header(&(prologue->header), PROLOGUE_SIZE, ALLOC);

    // (2) set prologe footer - size: HEADER_SIZE+FOOTER_SIZE, alloc_info: alloc

    set_footer(&(prologue->footer), PROLOGUE_SIZE, ALLOC);

}



/* set_epilogue: create a epilogue contains a header

 * input: start addr 

 * output: void

 */

static void set_epilogue(Epilogue* epilogue)

{

    set_header(&(epilogue->header), 0, ALLOC);// set prologe header - size: 0, alloc_info: alloc

}



/* set_prev_alloc_info: store if previous block is free in the second last bit of header

 * input: (1) header ptr (2) free or alloc 

 * output: void

 */

static void set_prev_alloc_info(Hdft* header, size_t prev_alloc_info)

{

        header->size = (header->size & ~0x2) | prev_alloc_info; //set second last bit 1 if prev alloc

}



/* get_size: obtain the size of a block in the header/footer

 * input: header/footer pointer 

 * output: size of the block

 */

static size_t get_size(Hdft* hdft)

{

    size_t blk_size = hdft->size & ~0xF; // size is size clear alloc info

    return blk_size;

}



/* get_alloc: obtain the alloc/free info of the block

 * input: header/footer pointer 

 * output: alloc or free

 */

static size_t get_alloc(Hdft* hdft)

{

    return hdft->size & 0x01; // get the last bit of size, which is the alloc/free info

}



/*  get_prev_alloc: obtain the alloc/free info of the prev block

 * input: header/footer pointer 

 * output: alloc or free

 */

static size_t get_prev_alloc(Hdft* hdft)

{

    return (hdft->size & 0x2) >> 1; // get the second last bit of size, then right move 1to get free/alloc

}



/* list_init: 

 * input: init free list, which contains a head and a tail

 * output: void

 */

static void list_init(FreeList* head)

{

    head->prev = head;   

    head->next = head;

}



/* # at_list_end: Judge if is at the end of a list

 * input: node pointer

 * output: true if is at end, false is not 

 */

static bool at_list_end(FreeList* hd_ptr, FreeList* nd_ptr)

{

    // check if the next ptr is null, only the tail node's next is null

    if(nd_ptr == hd_ptr){

        return true;

    } else{

        return false;

    }

}



/*  node_add: add a node to the head of a list

 * input: (1) head node (2) node pointer

 * output: void

 */

static void node_add(FreeList* hd_ptr, FreeList* nd_ptr)

{

    FreeList* tmp_ptr = hd_ptr->next; //record next node

    hd_ptr->next = nd_ptr;           //link new node to head 

    nd_ptr->next = tmp_ptr;         //link next node to new node

    tmp_ptr->prev = nd_ptr;         //set next node prev to new node 

    nd_ptr->prev = hd_ptr;         //set new node prev to head

}



/* node_del: delete a list

 * input: node ptr to be deleted

 * output: void

 */

static void node_del(FreeList* nd_ptr)

{

    nd_ptr->next->prev = nd_ptr->prev; // set next prev to prev node

    nd_ptr->prev->next = nd_ptr->next; // set prve next to next node



}



/* find_block: find the fit block, if not found, expand the heap

 * input: payload size request 

 * output: pointer to the payload of the block

 */

static void* find_block(size_t payload_size)

{

    // if size is 0, return NULL

    if(payload_size == 0){

        return NULL;

    }

    size_t size_needed = align(payload_size + HDFT_SIZE); // compute real size 

    void* list_hd_ptr = size_switch(size_needed); // decide which list to search by size

    void* pld_ptr = check_size(list_hd_ptr, size_needed); // check in the free list if fit block exist

    if(pld_ptr == NULL){ // (1) such block does not exist

        return heap_exp(size_needed); // apply for expand heap, return  poiter to the payload 

    } else{ // (2) block found

        return fitin_block(pointer_move(pld_ptr, pld_to_hdcurr), size_needed); // fit in the block

       // return pld_ptr; // return  poiter to the payload 

    }

}



/* check_size: check if there exist an block that has sufficient space in the list

 * input: (1) head of the list (2) size request(after round up)

 * output: return the paylaod ptr if exist such a block, return NUll if no exist 

 */

static void* check_size(FreeList* list_hd_ptr, size_t size)

{

    FreeList* check_ptr = list_hd_ptr->next; // init check pointer to the start of the block

    FreeList* lt_head = freelist_start + (FREELISTNUM - 1) * sizeof(FreeList); // the last free list hd addr

    // loop to check for the size until reach the end of list

    while(1){

        // if not found in the cur freelist, go search in the larger list

        while(at_list_end(list_hd_ptr, check_ptr)){

            if(list_hd_ptr == lt_head){

                return NULL; // if not found in the largest list, return NULL to apply for extra space

            }

            list_hd_ptr++;  // search size in the next size list 

            check_ptr = list_hd_ptr->next; // move check pointer to the start of the block 

        }

        // if found it in the cur freelist return it

        if(get_size(pointer_move(check_ptr, pld_to_hdcurr)) >= size){

            return check_ptr; // return the payload ptr of the block

        }

        check_ptr = check_ptr->next; // move to check next node, go through the list

    } 

}



/* heap_exp: expend the heap 

 * input: size request(after round up)

 * output: pointer to the payload of new block

 */

static void* heap_exp(size_t size_needed)

{

    //(1) compute size and apply for new space

    void* ptr = mem_sbrk(size_needed); // apply for new space

    void* payload_ptr = NULL; // payload pointer

    if(ptr){ // heap can be expanded

        payload_ptr = ptr; // record the new block pay load

    } else{  //  if heap cannot be expaned, return empty pointer

        return NULL;

    }

    //(2) set new header

    ptr = pointer_move(ptr, pld_to_hdcurr); // move ptr to header

    set_header(ptr, size_needed, ALLOC); 

    size_t left_size = get_size(ptr) - size_needed;

    if(left_size >= MINBLOCKSIZE){

        void* new_hd = pointer_move(ptr, hdcurr_to_hdnext);

        set_header(new_hd, left_size, FREE); //create a new header for the splited block  

        void* new_ft = pointer_move(new_hd, hdcurr_to_ftcurr);

        set_footer(new_ft, left_size, FREE); //(2-5) update the old footer as the footer for splited block

        node_add(size_switch(left_size), pointer_move(pointer_move(ptr, hdcurr_to_hdnext), hdcurr_to_pld));//(2-6) add splited node to free list according to the size

    }

    //(3) set new epilogue

    set_epilogue(pointer_move(ptr, hdcurr_to_hdnext)); //move ptr to next header, which is the epi

    //(4) return pointer to payload of new block

    return payload_ptr;

}



/* coalesce_block: combine current block with the one next to it if both free

 * input: current header ptr

 * output: void

 */

static void coalesce_block(void* hd_ptr)

{

    // (1) gather size info of the next block

    size_t new_size = get_size(hd_ptr);

    void* hdptr_next = pointer_move(hd_ptr, hdcurr_to_hdnext); //find next header

    // (2-1) case1: only next block is free

    if(get_alloc(hdptr_next) == FREE && get_prev_alloc(hd_ptr) == ALLOC){

        new_size += get_size(hdptr_next); // gather next block size

        node_del(pointer_move(hdptr_next, hdcurr_to_pld)); //delete the next free block from free list  

        set_header(hd_ptr, new_size, FREE);              // update new size and set free for header

        set_footer(pointer_move(hd_ptr, hdcurr_to_ftcurr), new_size, FREE); // update new size and set free for footer

        node_add(size_switch(new_size), pointer_move(hd_ptr, hdcurr_to_pld)); // add new free block to free list by size

    } 

    // (2-2) case2: only prev block is free

    else if(get_alloc(hdptr_next) == ALLOC && get_prev_alloc(hd_ptr) == FREE){

        void* hdptr_prev = pointer_move(pointer_move(hd_ptr, hdcurr_to_ftprev), ftcurr_to_hdcurr); //find prev header

        new_size += get_size(hdptr_prev); // gather next block size

        node_del(pointer_move(hdptr_prev, hdcurr_to_pld)); //delete the prev free block from free list 

        set_header(hdptr_prev, new_size, FREE);              // update new size and set free for header

        set_footer(pointer_move(hdptr_prev, hdcurr_to_ftcurr), new_size, FREE); // update new size and set free for footer

        node_add(size_switch(new_size), pointer_move(hdptr_prev, hdcurr_to_pld)); // add new free block to free list by size     

    } 

    // (2-3) case3: both next and prev block are free

    else if(get_alloc(hdptr_next) == FREE && get_prev_alloc(hd_ptr) == FREE){

        void* hdptr_prev = pointer_move(pointer_move(hd_ptr, hdcurr_to_ftprev), ftcurr_to_hdcurr); //find prev header

        new_size += get_size(hdptr_prev) + get_size(hdptr_next); // gather next and prev block size

        node_del(pointer_move(hdptr_next, hdcurr_to_pld)); //delete the next free block from free list   

        node_del(pointer_move(hdptr_prev, hdcurr_to_pld)); //delete the prev free block from free list 

        set_header(hdptr_prev, new_size, FREE);              // update new size and set free for header

        set_footer(pointer_move(hdptr_prev, hdcurr_to_ftcurr), new_size, FREE); // update new size and set free for footer

        node_add(size_switch(new_size), pointer_move(hdptr_prev, hdcurr_to_pld)); // add new free block to free list by size     

    }

    //(2-4) case4: both next and prev block are ALLOC, do nothing

    else{

        return;

    }

}



/* fitin_block: if a free block is sufficient when malloc, return pld ptr, split it if it is big enough

 * input: (1) header ptr to the block to be split (2)size request 

 * output: void

 */

static void* fitin_block(void* hd_ptr, size_t size_needed)

{

    // (1) compute size left

    size_t left_size = get_size(hd_ptr) - size_needed;



    // (2) if size left is big enough for a block, split it

    if(left_size >= MINBLOCKSIZE){

        void* ft_ptr = pointer_move(hd_ptr, hdcurr_to_ftcurr); // record curr footer

        if(get_alloc(hd_ptr) == FREE)

            node_del(pointer_move(hd_ptr, hdcurr_to_pld)); //(2-2) del old block from free list

        set_header(hd_ptr, size_needed, ALLOC); //(2-1) update size info in the old block header 

        

        void* new_hd = pointer_move(hd_ptr, hdcurr_to_hdnext);

        set_header(new_hd, left_size, FREE); //(2-3) create a new header for the splited block 

        //(2-4) case1: the next block is free, coalease the splited block with next block

        if(get_alloc(pointer_move(new_hd, hdcurr_to_hdnext)) == FREE){

            coalesce_block(pointer_move(hd_ptr, hdcurr_to_hdnext));

        }

        //(2-4) case2: the next block is not free, add the splited block to free list

        else{

            set_footer(ft_ptr, left_size, FREE); //(2-5) update the old footer as the footer for splited block

            node_add(size_switch(left_size), pointer_move(pointer_move(hd_ptr, hdcurr_to_hdnext), hdcurr_to_pld));//(2-6) add splited node to free list according to the size

        }

        return pointer_move(hd_ptr, hdcurr_to_pld);

        

    // (3) if size left is not big enough, change the alloc info to ALLOC 

    } else{

        if(get_alloc(hd_ptr) == FREE)

            node_del(pointer_move(hd_ptr, hdcurr_to_pld)); //del old block from free list

        set_header(hd_ptr, get_size(hd_ptr), ALLOC); //change the alloc info to ALLOC 

        return pointer_move(hd_ptr, hdcurr_to_pld);

    }

}



/* min: compare two numbers, and return the smaller one (used for realloc memcpy)

 * input: (1) size1 (2) size2

 * output: the smaller size

 */

static size_t min(size_t size1, size_t size2)

{

    if(size1 <= size2)

        return size1;

    else

        return size2;

}



//////////////////////////////////////////////////

// mm functions

////////////////////////////////////////////////// 



/* 

 * mm_init: returns false on error, true on success.

 */

bool mm_init(void)

{   

    // rounds up to the nearest multiple of ALIGNMENT 

    size_t size = align(FREELISTNUM * sizeof(FreeList) + PROLOGUE_SIZE + EPILOGUE_SIZE); 

    freelist_start = mem_sbrk(size);// start of the heap: area of free list heads + Prologue + Epilogue 

    // Init all the free list heads

    for(char i = 0; i < FREELISTNUM; i++){

        list_init((void *)((char *)(freelist_start) + i * sizeof(FreeList)));

    }

    

    // Init prologue and epi

    Prologue* prologue = freelist_start+(FREELISTNUM*sizeof(FreeList)); //compute Prologue addr  

    set_prologue(prologue);                                               // init prologue

    Epilogue* epilogue = pointer_move(pointer_move(prologue, pad_to_hdcurr), hdcurr_to_hdnext); //move to epi

    set_epilogue(epilogue);                                               //init epilogue

    heap_start = epilogue ;

    mm_checkheap(__LINE__);

    return true;

}



/*

 * malloc

 */

void* malloc(size_t size)

{

    //(2) find the proper block using find_block func

    void * ptr = find_block(size);

    mm_checkheap(__LINE__);

    return ptr;

}



/*

 * free

 */

void free(void* ptr)

{

    //(1) check the validity of ptr

    if(ptr == NULL) // (1-1) if ptr is NULL, do nothing 

        return;

    //(2) free curr block

    void* hd_ptr = pointer_move(ptr, pld_to_hdcurr); // move ptr to the header



    //(2-1) if the adj block is free, coa them

    if(get_alloc(pointer_move(hd_ptr, hdcurr_to_hdnext)) == FREE || get_prev_alloc(hd_ptr) == FREE){

        coalesce_block(hd_ptr);

    }

    //(2-2) if only curr block is free, free it 

    else{

        set_header(hd_ptr, get_size(hd_ptr), FREE); // update alloc info in header

        set_footer(pointer_move(hd_ptr, hdcurr_to_ftcurr), get_size(hd_ptr), FREE); // update alloc info in footer

        node_add(size_switch(get_size(hd_ptr)), pointer_move(hd_ptr, hdcurr_to_pld)); // add new free block to free list by size

    }



    mm_checkheap(__LINE__);



    return;

}

/*

 * realloc

 */

void* realloc(void* oldptr, size_t size) //

{

    //(1) if oldptr is NULL, the call is equivalent to malloc(size)

    size = align(size + HDFT_SIZE); // compute real size 

    if(oldptr == NULL){

        malloc(size);

    }

    //(2) if size is 0, the call is equivalent to free(ptr)

    if(size == 0){

        free(oldptr);

        return NULL;

    }

    //(3) not NULL case

    void* ptr = pointer_move(oldptr, pld_to_hdcurr); // move back to the curr header

    //(3-1) If the old block is big enough, use it

    if(get_size(ptr) >= size){

        fitin_block(ptr, size);

        mm_checkheap(__LINE__);

        return oldptr;      

    }

    //(3-2) find a new block

    ptr = find_block(size);

    //(3-3) copy size content to the new block

    size_t size_copy = min(get_size(pointer_move(oldptr, pld_to_hdcurr))- HDFT_SIZE, size); //the size to copy is the min one between old size and new size

    mem_memcpy(ptr, oldptr, size_copy);   // copy the content to the new block

    free(oldptr);                     // the old block is free now, free it

    mm_checkheap(__LINE__);

    return ptr;

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

        mem_memset(ptr, 0, size);

    }

    return ptr;

}





/*

 * mm_checkheap

1. For blocks

    (1) header and footer size msg matches (done)

    (2) payload area is aligned (done)

    (3) No alloced blocks overlap (done)

    (4) No contiguous free blocks (done)

    (5) The prev free info in the header matches the prev block (done)

    (6) Size of each block is larger than min block size(32), an is a multiple of 16 (done)

2. For lists

    (1) Every block in the free list marked as free (done)

    (2) Every free block is in the free list (done)

    (3) next/prev pointers in a heap block point to valid heap addresses (done)

    (4) Each segregated list only has its own size blocks (done)

    (5) The doule direction linked list is correct (prev->next = next->pre) (done)

3. For the heap

    (1) All blocks are in the heap boundries (done)

 */



/* 

 *  1-1 header and footer size and alloc msg matches

 */

static bool hdft_match(Hdft* hd_ptr)

{

    Hdft* ft_ptr = pointer_move(hd_ptr, hdcurr_to_ftcurr);

    return get_size(hd_ptr) == get_size(ft_ptr);

}



/*

 *  1-2 payload area is aligned

 */

static bool aligned(const void* p)

{

    size_t ip = (size_t) p;

    return align(ip) == ip;

}



/* 

 *  1-5 The prev free info in the header matches the prev block

 */

static bool prev_alloc_match(Hdft* hd_ptr)

{

    if(get_size(hd_ptr)){ 

        Hdft* next_hd_ptr = pointer_move(hd_ptr, hdcurr_to_hdnext);

        return get_alloc(hd_ptr) == get_prev_alloc(next_hd_ptr);

    } else{ // epi does not have next

        return true;

    }



} 



/* 

 *  1-6 Size of each block is larger than min block size, and is a multiple of 16

 */

static bool block_size_valid(size_t blk_size)

{

    //(1)  Size of each block is larger than min block size(except epi)

    if(blk_size != 0 && blk_size < MINBLOCKSIZE){

        dbg_printf("Block size is %ld, less than 32!!!\n", blk_size);

        return false;

    }

    //(2) Block size is a multiple of 16

    if(blk_size % 16 != 0){

        dbg_printf("Block size is %ld, not a multiple of 16!!!\n", blk_size);

        return false;

    }

    return true;

}





/* 

 * 3-1  Return wether a ptr are in the heap boundries

 */

static bool in_heap(const void* p)

{

    return p <= mem_heap_hi() && p >= mem_heap_lo();

}



/* 

 *  2-2Every free block is in the free list 

 */

static bool is_in_list(Hdft* blk_hd)

{

    size_t blk_size = get_size(blk_hd); // get size of the free block

    FreeList* list_hd = size_switch(blk_size); //choose corrsponding list head 

    FreeList* nd_ptr = pointer_move(blk_hd, hdcurr_to_pld); // the node ptr to becheck 

    FreeList* check_ptr = list_hd->next; // move checker(which would go through the list) to the frist node 



    while(!at_list_end(list_hd, check_ptr)){ //go through the list until the end 

        if(check_ptr == nd_ptr) return true; // if the node to be check is found return true

        check_ptr = check_ptr->next;         // if not found move check the next node

    }

    return false; 

}



/* 

 *  2-4 Each segregated list only has its own size blocks 

 */

static bool size_fit(int i, size_t size)

{   // for each size, if exist block not in the proper size, return false

    switch (i){

    case 0:

        if(size <= SIZE32) return true;

        else{

             dbg_printf("size32 list has size %ld block!!!\n", size);

             return false;

        }

     case 1:

        if(size > SIZE32 && size <= SIZE64) return true;

        else{

             dbg_printf("size64 list has size %ld block!!!\n", size);

             return false;

        }

    case 2:

        if(size > SIZE64 && size <= SIZE128) return true;

        else{

             dbg_printf("size128 list has size %ld block!!!\n", size);

             return false;

        }

    case 3:

        if(size > SIZE128 && size <= SIZ256) return true;

        else{

             dbg_printf("size256 list has size %ld block!!!\n", size);

             return false;

        }

    case 4:

        if(size > SIZ256 && size <= SIZE512) return true;

        else{

             dbg_printf("size512 list has size %ld block!!!\n", size);

             return false;

        }       

    case 5:

        if(size > SIZE512 && size <= SIZE1024) return true;

        else{

             dbg_printf("size1024 list has size %ld block!!!\n", size);

             return false;

        }

     case 6:

        if(size > SIZE1024 && size <= SIZE2048) return true;

        else{

             dbg_printf("size2048 list has size %ld block!!!\n", size);

             return false;

        }

    case 7:

        if(size > SIZE2048 && size <= SIZE4096) return true;

        else{

             dbg_printf("size4096 list has size %ld block!!!\n", size);

             return false;

        }

    case 8:

        if(size > SIZE4096 && size <= SIZE8192) return true;

        else{

             dbg_printf("size8192 list has size %ld block!!!\n", size);

             return false;

        }

    case 9:

        if(size > SIZE8192 && size <= SIZE16384) return true;

        else{

             dbg_printf("size16384 list has size %ld block!!!\n", size);

             return false;

        }

    case 10:

        if(size > SIZE16384) return true;

        else{

             dbg_printf("sizelt16384 list has size %ld block!!!\n", size);

             return false;

        }      

    default:

        return false;

    }



}





bool mm_checkheap(int lineno)

{

#ifdef DEBUG

void* hd_ptr = heap_start; // move head ptr to the start of the heap

char contiguous = 0;  //flag used to check contiguous block, if it is greater than two, bug found 

void* prev_pld_start = NULL; //record the start of prev pld, used to check if any payload overlpas

void* prev_pld_end = NULL;  //record the end of prev pld,used to check if any payload overlpas

void* cur_pld_start = NULL; //record the start of cur pld,used to check if any payload overlpas

void* cur_pld_end = NULL; //record the end of cur pld,used to check if any payload overlpas



    //go through the heap block by block

    while(1){ 

        //3-1 check all blocks are in the heap boundries

        if(!in_heap(hd_ptr)){

            dbg_printf("BLOCK IS OUTOF BOUNDRY!!!\n");

            return false;

        } 



        //1-2 check payload area is aligned

        if(!aligned(pointer_move(hd_ptr, hdcurr_to_pld))){

             dbg_printf( "PAYLOAD IS NOT ALIGNED!!!\n");

             return false;

        } 



        //1-5 The prev free info in the header matches the prev block

        if(!prev_alloc_match(hd_ptr)){

             dbg_printf("PREV ALLOC INFO NOT MATCH!!!\n");

             dbg_printf("cur_size:%ld\n", get_size(hd_ptr));

             fprintf(stderr, "PREV:%ld, CURR:%ld\n",get_prev_alloc(pointer_move(hd_ptr, hdcurr_to_hdnext)),get_alloc(hd_ptr));

             return false;

        } 



        //1-6 Size of each block is larger than min block size(32), an is a multiple of 16

        if(!block_size_valid(get_size(hd_ptr))){

            return false;

        }



        if(get_alloc(hd_ptr) == FREE){ // FREE block

            //1-4 check no contiguous free blocks

            //fprintf(stderr, "Free(size:%ld)->",get_size(hd_ptr));

            contiguous++; //add 1 if find a free block

            if(contiguous > 1){

                dbg_printf("CONTIGUOUS FREE BLOCKS!!!\n");

                return false;

            }



            //1-1 check header and footer size and alloc msg matches

            if(!hdft_match(hd_ptr)){

                dbg_printf( "HEADER AND FOOTER ARE NOT MATCH!!!\n");

                return false;

            } 



            //2-2 Check free block is in the free list

            if(!is_in_list(hd_ptr)){

                dbg_printf("FREE BLOCK NOT IN THE LIST!!!\n"); 

                return false;

            } 

            



        } else{ // ALLOC block

            //fprintf(stderr, "ALLOC(size:%ld)->",get_size(hd_ptr));

            contiguous = 0;

            //1-3 check No alloced blocks overlap

            cur_pld_start = pointer_move(hd_ptr, hdcurr_to_pld);//find current pauyload start 

            cur_pld_end = pointer_move(hd_ptr, hdcurr_to_hdnext); //find current pauyload end 

            if(cur_pld_start < prev_pld_end){ // if the two addr overlaps, return error

                dbg_printf( "Payload(%p:%p) overlaps another payload (%p:%p)\n", prev_pld_start,prev_pld_end,cur_pld_start,cur_pld_end );

                return false;

            }else{ // if not overlaps, update the prev pld to cur

                prev_pld_start = cur_pld_start;

                prev_pld_end = cur_pld_end;

            }

        }

        // finish if reach the end of the heap 

        if(get_size(hd_ptr) == 0){

            //fprintf(stderr, "\n");

            break;

        } else{

            hd_ptr = pointer_move(hd_ptr, hdcurr_to_hdnext); // move to next block

        }

    }



    // check through the all the segragate list node by node 

    FreeList* list_hd = NULL;

    FreeList* checker = NULL;

    Hdft* blk_hd = NULL;

    for(char i = 0; i < FREELISTNUM; i++){

        list_hd = freelist_start + i * sizeof(FreeList); // find the free list head  

        checker = list_hd->next; // move checker to the first node

        while(!at_list_end(list_hd, checker)){

            // 2-1 Every block in the free list marked as free

            blk_hd = pointer_move(checker, pld_to_hdcurr); // find block head

            if(get_alloc(blk_hd) != FREE){

                dbg_printf("BLOCK IN FREE LIST IS NOT MARKED FREE!!!\n");

                return false;

            }



            // 2-3 next/prev pointers in a heap block point to valid heap addresses

            if(!in_heap(checker->next) || !in_heap(checker->prev) || !aligned(checker->next) || !aligned(checker->prev)){

                dbg_printf("next/prev pointers in a heap block point to invalid heap addresses!!!\n");

                return false;                

            }



            // 2-4 Each segregated list only has its own size blocks

            if(!size_fit(i, get_size(blk_hd))){

                return false;               

            }



            // 2-6 The doule direction linked list is correct

            if(checker->prev->next != checker || checker->next->prev != checker){

                dbg_printf("Doule direction linked list fault!!!\n");

                return false;                

            }



            checker = checker->next; // move to the next node inthe list 

        }

    }

#endif // DEBUG

    return true;

}





