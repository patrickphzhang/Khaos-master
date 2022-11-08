#include <stdio.h>
#include <stdint.h>
#include <stdarg.h>
#include <stdlib.h>
#include <sys/mman.h>
#include <unistd.h>
#define INLINEATTR __attribute__((always_inline, used))
#define PTRVALMASK 0xfffffffffff0
#define CTRLBITMASK  0x4
#define CTRLSIGNMASK 0x8

// #define PTRSIZEBITS 0
// #define PTRVALMASK ((1ULL << PTRSIZEBITS) - 1ULL)
// #define CTRLBITMASK  ((1ULL << PTRSIZEBITS))
// #define CTRLSIGNMASK ((1ULL << (PTRSIZEBITS + 1)))
// #define PAGE_ALIGNED 0xFFFFFFFFFFFFF000
// #define PAGE_SIZE 0x1000
// bool tagged = false;

// struct GlobalUseEntry {
//     void * base;
//     uint64_t offset;
//     uint64_t tag;
// };
// extern GlobalUseEntry* FusionArray;
// extern uint64_t FusionArraySize;
extern "C" {

    // void change_permission(uint64_t addr, uint64_t size, uint64_t prot) { 
    //     // modify page permission to Write&Read
    //     uint64_t begin_addr = addr & PAGE_ALIGNED; // begin addr must be aligned to page size
    //     uint64_t end_addr = ((addr + size) & PAGE_ALIGNED) + PAGE_SIZE;
    //     uint64_t length = end_addr - begin_addr; // legnth must be an integer multiple of 0x1000
    //     // printf("begin addr: %llx\n", begin_addr);
    //     // printf("length: %llx\n", length);
    //     int res = mprotect((void *)begin_addr, length, prot);
    //     if (res != 0) {
    //         printf("[Error] 1 mprotect error\n");
    //         exit(-1);
    //     }
    // }

    INLINEATTR void* extract_ptrval(const void* ptr) {
        void* ptrval = (void*)((uintptr_t)ptr & PTRVALMASK);
        return ptrval;
    }

    INLINEATTR uint8_t extract_ctrlbit(const void* ptr) {
        uint8_t ctrlbit = (uint8_t)(((uintptr_t)ptr & CTRLBITMASK) >> 2);
        // printf("ctrlbit: %d\n", ctrlbit);
        return ctrlbit;
    }

    INLINEATTR uint8_t extract_ctrlsign(const void* ptr) {
        uint8_t ctrlsign = (uint8_t)(((uintptr_t)ptr & CTRLSIGNMASK) >> 3);
        // printf("ctrlsign: %d\n", ctrlsign);
        return ctrlsign;
    }

    INLINEATTR uint8_t get_random(uint8_t ctrl) {
        // return (rand()%(RAND_MAX - 1) + 1);
        return ctrl & 0x1;
    }

    // void* combine_ptr(const void* ptrval, uint8_t ctrlbit) {
    //     // if ((uintptr_t)ptrval & 0x6) {
    //     //     printf("we are using these two bits, wtf?");
    //     //     exit(-1);
    //     // }
    //     uintptr_t ptr = (uintptr_t)(ctrlbit << 1);
    //     ptr |= (uintptr_t)ptrval;
    //     ptr |= (uintptr_t)(1 << 2);
    //     return (void*)ptr;
    // }

    // void combine_global_use_ptr() {
    //     if (FusionArraySize <= 0)
    //         return;
    //     // printf("FusionArray: %llx\n", &FusionArray);
    //     uint64_t *it = (uint64_t*)&FusionArray;
    //     // printf("FusionArraySize: %ld\n", FusionArraySize);
    //     struct GlobalUseEntry *GlobalUseI = (struct GlobalUseEntry *)&FusionArray;
    //     uint64_t BeginAddr = UINT64_MAX, EndAddr = 0;
    //     for (uint64_t i = 0; i < FusionArraySize; i++) {
    //         // printf("GlobalUseI: %p\n", GlobalUseI);
    //         // GlobalUseI = (GlobalUseEntry*)it;
    //         uint64_t position = (uint64_t)GlobalUseI->base + GlobalUseI->offset;
    //         if (position < BeginAddr)
    //             BeginAddr = position;
    //         if (position + 8 > EndAddr)
    //             EndAddr = position + 8;
    //         GlobalUseI++;
    //     }
    //     change_permission(BeginAddr, EndAddr - BeginAddr, PROT_WRITE | PROT_READ);
    //     // TODO: chang the permission back
    //     GlobalUseI = (struct GlobalUseEntry *)&FusionArray;
    //     for (uint64_t i = 0; i < FusionArraySize; i++) {
    //         // printf("Base: %llx\n", GlobalUseI->base);
    //         // printf("Offset: %ld\n", GlobalUseI->offset);
    //         // printf("Tag: %ld\n", GlobalUseI->tag);
    //         // add tag to the use
    //         uint64_t *position = (uint64_t*)((uint64_t)GlobalUseI->base + GlobalUseI->offset);
    //         uint64_t content = *position;
    //         *position = (uint64_t)(combine_ptr((void*)content, GlobalUseI->tag));
    //         GlobalUseI++;
    //     }
    //     // change_permission(BeginAddr, EndAddr - BeginAddr, PROT_READ);
    // }
    // args: 
    // ptr -- callee of the indirect call, contains ctrl bit and fusion function's argument number in the high bits
    // count -- the number of arguments of indirect call
    // pointers -- pointers to the arguments of indirect call
    //
    // function: 
    // 1. extract the ctrl bit
    // 2. extract the number of fusioned function's argument
    // 3. based on 1 & 2, conduct the argumets, then call
    // void* test(const void* ptrval, int count, ...) {
        // uint8_t ctrlbit = extract_ctrlbit(ptrval);
        // uint32_t argnum = extract_argno(ptrval);
        // void * target = extract_ptrval(ptrval);
        // // check if it's a tagged pointer 
        // if (!argnum) {
        //     // call target with origin arguments
        //     //((int (*)(...))target)(...);
        // }
        
        // va_list valist;
        // // init valist  
        // va_start(valist, count); 
        // // for (i = 0; i < num; i++) { 
        // //     sum += va_arg(valist, int); 
        // // } 

        // // collect valist 
        // va_end(valist);
    //}
}