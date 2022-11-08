#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

#include <string.h>

#ifdef _WIN32
#include <windows.h>
#include <winternl.h>
#include <tchar.h>
extern "C" const IMAGE_DOS_HEADER __ImageBase;
#endif

#ifdef __linux__
#include <elf.h>
#include <unistd.h>
#include <cstring>
#include <sys/auxv.h>
#include <sys/mman.h>
const void *_smc_start;
const void *_smc_end;
const void *_rodata_start;
const void *_rodata_end;
typedef unsigned long DWORD ;
typedef DWORD *PDWORD;
#endif
#if defined(_WIN64)||defined(__x86_64__)  //64bit
typedef unsigned long long ADDR;
#define PAGE_ALIGNED 0xFFFFFFFFFFFFF000
#define SMC_END 0xFFFFFFFFFFFFFFFF
#define RELOC_SIZE 8
#endif // __linux__

#if (defined(_WIN32) && !defined(_WIN64))||defined(__i386__)  //32bit
typedef unsigned long ADDR;
#define PAGE_ALIGNED 0xFFFFF000
#define SMC_END 0xFFFFFFFF
#define RELOC_SIZE 4
#endif

#define PAGE_SIZE 0x1000
bool decrypted = false;

union xor_key {
  uint64_t key_i;
  unsigned char key_c[sizeof(uint64_t)];
};
ADDR *smc_start, *smc_end;
ADDR *rodata_start, *rodata_end;
ADDR text_start=0, text_end=0;
ADDR rdata_start=0, rdata_end=0;
ADDR *RelocItems = nullptr;

enum reloc_type{           
  ABSOLUTE_T,
  HIGH,
  LOW,
  HIGHLOW,
  HIGHADJ,
  MACHINE_SPECIFIC_5,
  RESERVED,
  MACHINE_SPECIFIC_7,
  MACHINE_SPECIFIC_8,
  MACHINE_SPECIFIC_9,
  DIR64
};

// static void print(const char * desc, int val) {
//   puts(desc);
//   char buffer[20];
//   itoa(val, buffer, 16);
//   puts(buffer);
// }

static PDWORD ModifyPagePermissionToWRX(
    ADDR func_addr,
    unsigned long size) { // modify page permission ti Write&Read&Excution

  /*if ((func_addr >= data_start) && (func_addr <= data_end)) {
  return;
}*/
  PDWORD pflOldProtect = (PDWORD)malloc(sizeof(DWORD));
  ADDR begin_addr =
      func_addr & PAGE_ALIGNED; // begin addr must be aligned to page size
  ADDR end_addr = ((func_addr + size) & PAGE_ALIGNED) + PAGE_SIZE;
  unsigned long length =
      end_addr - begin_addr; // legnth must be an integer multiple of 0x1000

#ifdef __linux__
  int res =
      mprotect((void *)begin_addr, length, PROT_EXEC | PROT_READ | PROT_WRITE);
  if (res != 0) {
    // printf("[Error] 1 mprotect error\n");
    exit(-1);
  }
  *pflOldProtect = PROT_READ | PROT_WRITE;
  return pflOldProtect;
#endif
#ifdef _WIN32

  int res = VirtualProtect((void *)begin_addr, length, PAGE_EXECUTE_READWRITE,
                           pflOldProtect);
  if (res == 0) {

    puts("[Error] VirtualProtect error1\n");
    exit(-1);
  }
  // puts("[Success] VirtualProtect Sucess\n");
  return pflOldProtect;
#endif // _WIN32
}
/// <summary>
/// Determine whether the current modules has been decrypted
/// </summary>
/// <returns></returns>
#ifdef _WIN32
static bool HasBeenDecrypted(ADDR BaseAddr) {
  // print("in HasBeenDecrypted", 0);
  ADDR lpMapAddr = BaseAddr;
  PIMAGE_DOS_HEADER pDosHeader = (PIMAGE_DOS_HEADER)lpMapAddr;
  PIMAGE_NT_HEADERS pNtHeader =
      (PIMAGE_NT_HEADERS)(pDosHeader->e_lfanew + lpMapAddr);
  PIMAGE_FILE_HEADER pFileHeader =
      (PIMAGE_FILE_HEADER) & (pNtHeader->FileHeader);
  PIMAGE_SECTION_HEADER pFirstSectionHeader = IMAGE_FIRST_SECTION(pNtHeader);
  for (int i = 0; i < pFileHeader->NumberOfSections; i++) {
    PIMAGE_SECTION_HEADER pSectionHeader = (PIMAGE_SECTION_HEADER)(
        (ADDR)pFirstSectionHeader + i * IMAGE_SIZEOF_SECTION_HEADER);

    if (strstr((const char *)(pSectionHeader->Name), ".smcsec")) {
      if (pSectionHeader->Misc.VirtualSize == 0)
        return true;
      continue;
    }
  }
  return false;
}
#endif
/*
    Modify page permission of given function to Read&Excution
*/
static void ModifyPagePermissionToOldProtect(
    ADDR func_addr, unsigned long size,
    PDWORD pflOldProtect) { // modify page permission ti Read&Excution
  /*if ((func_addr >= data_start) && (func_addr <= data_end)) {
    return;
  }*/
  ADDR begin_addr =
      func_addr & PAGE_ALIGNED; // begin addr must be aligned to page size
  ADDR end_addr = ((func_addr + size) & PAGE_ALIGNED) + PAGE_SIZE;
  unsigned long length =
      end_addr - begin_addr; // legnth must be an integer multiple of 0x1000
#ifdef __linux__
  int res = mprotect((void *)begin_addr, length, PROT_READ | PROT_EXEC);
#endif
#ifdef _WIN32
  PDWORD lpflOldProtect = 0;
  int res = VirtualProtect((void *)begin_addr, length, *pflOldProtect,
                           lpflOldProtect);
#endif // _WIN32
  if (res != 0) {
    puts("[Error] mprotect error\n");
    exit(-1);
  }
  // puts("[Success] VirtualProtect Sucess\n");
}

#ifdef _WIN32
static void GetSectionInfoInPE(ADDR BaseAddr) { 
    //clear all addr
    smc_start = smc_end = nullptr;
    text_start = text_end = rdata_start = rdata_end = 0;
    // On Windows, parse the pe header to get the start and end address of .smcsec , .text and .rdata section
    ADDR lpMapAddr = BaseAddr;
    PIMAGE_DOS_HEADER pDosHeader = (PIMAGE_DOS_HEADER)lpMapAddr;
    PIMAGE_NT_HEADERS pNtHeader =
      (PIMAGE_NT_HEADERS)(pDosHeader->e_lfanew + lpMapAddr);
    PIMAGE_FILE_HEADER pFileHeader =
      (PIMAGE_FILE_HEADER) & (pNtHeader->FileHeader);
    PIMAGE_SECTION_HEADER pFirstSectionHeader = IMAGE_FIRST_SECTION(pNtHeader);
    for (int i = 0; i < pFileHeader->NumberOfSections; i++) {
      PIMAGE_SECTION_HEADER pSectionHeader = (PIMAGE_SECTION_HEADER)(
          (ADDR)pFirstSectionHeader + i * IMAGE_SIZEOF_SECTION_HEADER);
      
      if (strstr((const char *)(pSectionHeader->Name), ".smcsec")) {
        //puts("found smcsec");
        ADDR SMCStart = pSectionHeader->VirtualAddress + lpMapAddr;
        ADDR SMCEnd = pSectionHeader->Misc.VirtualSize + SMCStart;
        smc_start = (ADDR*)SMCStart;
        smc_end = (ADDR *)SMCEnd;

        PDWORD poldpermistion = ModifyPagePermissionToWRX((ADDR)pSectionHeader, 0x1000);
        pSectionHeader->Misc.VirtualSize = 0;
        ModifyPagePermissionToOldProtect((ADDR)pSectionHeader, 0x1000,
                                         poldpermistion);
        
        continue;
      }

      if (strstr((const char *)(pSectionHeader->Name), ".text")) {
        //print("found text SizeOfRawData", pSectionHeader->SizeOfRawData);
        text_start = pSectionHeader->VirtualAddress;
        //printf("text addr: %x\n", text_start + lpMapAddr);
        /*PIMAGE_SECTION_HEADER pnSectionHeader = (PIMAGE_SECTION_HEADER)(
            (ADDR)pFirstSectionHeader + (i + 1) * IMAGE_SIZEOF_SECTION_HEADER);
        text_end = pnSectionHeader->VirtualAddress; */     
        text_end = pSectionHeader->Misc.VirtualSize + text_start;
        continue;
      }
      if (strstr((const char *)(pSectionHeader->Name), ".rdata")) {
        //puts("found rdata");

        rdata_start = pSectionHeader->VirtualAddress;
        // printf("text addr: %x\n", text_start + lpMapAddr);
        /*PIMAGE_SECTION_HEADER pnSectionHeader = (PIMAGE_SECTION_HEADER)(
            (ADDR)pFirstSectionHeader + (i + 1) * IMAGE_SIZEOF_SECTION_HEADER);
        rdata_end = pnSectionHeader->VirtualAddress;   */   
        rdata_end =
            pSectionHeader->Misc.VirtualSize + rdata_start ;
        continue;
      }
    }

}

static bool isInTextSection(ADDR virtualaddr) {
  if (virtualaddr >= text_start && virtualaddr <= text_end) {
    return true;  
  }
  return false;
}
static bool isInRdataSection(ADDR virtualaddr) {
  if (virtualaddr >= rdata_start  &&
      virtualaddr <= rdata_end ) {
    return true;
  }
  return false;
}
    /*
    Return the addresses of all relocation items in the .text section
    witch type is not ABSOLUTE
    */
static void GetRelocationInfoInPE(ADDR BaseAddr) {
    if (RelocItems != nullptr)
        free(RelocItems);
    ADDR lpMapAddr = BaseAddr;
    PIMAGE_DOS_HEADER pDosHeader = (PIMAGE_DOS_HEADER)lpMapAddr;
    PIMAGE_NT_HEADERS pNtHeader =  (PIMAGE_NT_HEADERS)(pDosHeader->e_lfanew + lpMapAddr);
    PIMAGE_OPTIONAL_HEADER pOptionalHeader = (PIMAGE_OPTIONAL_HEADER) & (pNtHeader->OptionalHeader);
    PIMAGE_DATA_DIRECTORY pDataDirectory = pOptionalHeader->DataDirectory;
    PIMAGE_BASE_RELOCATION pBaseRelocation = (PIMAGE_BASE_RELOCATION)(
        (ADDR)lpMapAddr + pDataDirectory[5].VirtualAddress);

    if (pBaseRelocation == nullptr)
      exit(-1);


    unsigned long Size = 0;
    unsigned long BlockSize = 0;
    while (BlockSize < pDataDirectory[5].Size&&
           (isInTextSection(pBaseRelocation->VirtualAddress) ||
            isInRdataSection(pBaseRelocation->VirtualAddress))) { // First Pass for calculate the Size of relocs we needed
      PWORD pRelocation =
          (PWORD)((ADDR)pBaseRelocation + sizeof(IMAGE_BASE_RELOCATION));
      DWORD NumberOfRelocationAddress =
          (pBaseRelocation->SizeOfBlock - sizeof(IMAGE_BASE_RELOCATION)) / 2;
     
      for (unsigned int i = NumberOfRelocationAddress; i > 0;
           pRelocation++, i--) 
      {
        ADDR RVA = (*pRelocation & 0xfff) | pBaseRelocation->VirtualAddress;
        int type = (*pRelocation & 0xf000) >> 12;
        if (type != ABSOLUTE_T) {
          Size++;
        }

      }
      BlockSize += pBaseRelocation->SizeOfBlock;
      pBaseRelocation = (PIMAGE_BASE_RELOCATION)((ADDR)pBaseRelocation +
                                                 pBaseRelocation->SizeOfBlock);
    }

    //printf("Size: %d\n", Size);
    RelocItems = (ADDR *)malloc((Size+1) * sizeof(ADDR));
    RelocItems[0] = Size;       
    pBaseRelocation = (PIMAGE_BASE_RELOCATION)(
        (ADDR)lpMapAddr +
        pDataDirectory[5]
            .VirtualAddress); // The first item of Relocs is the size of Relocs
    int index = 1;
    while (index <= Size &&
           (isInTextSection(pBaseRelocation->VirtualAddress) ||
            isInRdataSection(pBaseRelocation->VirtualAddress)) &&
            pBaseRelocation->SizeOfBlock) {                               // Second Pass for gather all reloc item'RVA we needed  
      PWORD pRelocation =
          (PWORD)((ADDR)pBaseRelocation + sizeof(IMAGE_BASE_RELOCATION));
      DWORD NumberOfRelocationAddress =
          (pBaseRelocation->SizeOfBlock - sizeof(IMAGE_BASE_RELOCATION)) / 2;
      for (unsigned int i = NumberOfRelocationAddress; i > 0;
           pRelocation++, i--) // 
      {
        ADDR RVA = (*pRelocation & 0xfff) | pBaseRelocation->VirtualAddress;
        
        int type = (*pRelocation & 0xf000) >> 12;

        if (type != ABSOLUTE_T) {
          RelocItems[index] = RVA;
          index++;
        }
      }
      pBaseRelocation = (PIMAGE_BASE_RELOCATION)((ADDR)pBaseRelocation +
                                                 pBaseRelocation->SizeOfBlock);
    }

   

}
#endif


static uint64_t GenerateKey64(){
    return 0x123456789abcdef;
}

/*
    Modify page permission of given function to Write&Read&Excution
*/


/// <summary>
/// Determine whether the current process is a dll file
/// </summary>
/// <returns></returns>
#ifdef _WIN32
static bool IsDll() {
    ADDR lpMapAddr = (ADDR)&__ImageBase;
    PIMAGE_DOS_HEADER pDosHeader = (PIMAGE_DOS_HEADER)lpMapAddr;
    PIMAGE_NT_HEADERS pNtHeader = (PIMAGE_NT_HEADERS)(pDosHeader->e_lfanew + lpMapAddr);
    if ((pNtHeader->FileHeader.Characteristics & IMAGE_FILE_DLL) ==
        IMAGE_FILE_DLL)
      return true;
    return false;
}
#endif

/// <summary>
/// An assembly function
/// Get the process control block(PEB) of this process
/// </summary>
/// <returns></returns>
#ifdef _WIN32
extern "C" PVOID64 _cdecl GetPeb();
#endif

/// <summary>
/// Get the load base addresses of all dependent dlls of this process
/// </summary>
/// <returns>
/// UINT64[n] DllBaseAddrs, base addresses of all dependent dlls, end with "-1"
/// </returns>
/// Fixme:  Redundant code
#ifdef _WIN32
static UINT64* GetAllModuleBase() {

  UINT64 *DllBaseAddrs = nullptr;
  struct _LIST_ENTRY *link, *item;
  struct _PEB *peb;
  struct _PEB_LDR_DATA *ldr;
  int size = 0;
  peb = (_PEB *)GetPeb();
  ldr = peb->Ldr;
  link = &ldr->InMemoryOrderModuleList;
  for (item = link->Flink; item != link; item = item->Flink) {
    struct _LDR_DATA_TABLE_ENTRY *entry = CONTAINING_RECORD(
        item, struct _LDR_DATA_TABLE_ENTRY, InMemoryOrderLinks);
    size++; 
  }
  DllBaseAddrs = (UINT64*)malloc(sizeof(UINT64) * (size + 1));
  int index = 0;
  for (item = link->Flink; item != link; item = item->Flink) {
    struct _LDR_DATA_TABLE_ENTRY *entry = CONTAINING_RECORD(
        item, struct _LDR_DATA_TABLE_ENTRY, InMemoryOrderLinks);

    DllBaseAddrs[index] = (UINT64)entry->DllBase;

    index++;
  }
  DllBaseAddrs[index] = -1;
  return DllBaseAddrs;
}
#endif

/// <summary>
/// decrypt function : decrypt the data in [func_addr : func_addr+size]
/// </summary>
/// <param name="func_addr"></param>
/// <param name="size"></param>
/// <param name="reloc_start"></param>
/// <param name="reloc_end"></param>
static void smc_decrypt(ADDR func_addr, unsigned long size, ADDR reloc_start,ADDR reloc_end, ADDR BaseAddr){
    #ifdef __linux__
    PDWORD pflOldProtect=ModifyPagePermissionToWRX(func_addr, size);
    #endif
   

    xor_key key;
    key.key_i = GenerateKey64();

    int *RelocsInCurrentFunction = nullptr;                 
    // Store the relative offset of all relocation items in the function  to the start address of the function
#ifdef _WIN32
    
    unsigned long SizeofRelocs = RelocItems[0];       
    // The First item in Relocs is the size of Relocs                 
    if (reloc_start >= 0 && reloc_end <= SizeofRelocs &&
        reloc_start != SMC_END) { // If reloc index is valid
      RelocsInCurrentFunction =
          (int *)malloc((reloc_end - reloc_start + 1) * sizeof(int));
      int index = 0;
      for (int i = reloc_start; i <= reloc_end; i++) {
        RelocsInCurrentFunction[index] = RelocItems[i + 1] - (func_addr-BaseAddr);
        index++;
      }
    }
#endif // _WIN32

    int IndexInRelocs = 0;
    for(int i = 0; i < size; i++){
      if (RelocsInCurrentFunction != nullptr &&
          i == RelocsInCurrentFunction[IndexInRelocs] &&
          IndexInRelocs <= reloc_end - reloc_start + 1) {
        IndexInRelocs++;
        i += RELOC_SIZE-1;                                    
        continue;
      }
      
        uint8_t byte = *(uint8_t *)(func_addr + i);
        //print("byte:", byte);
        byte = byte ^  key.key_c[i % sizeof(uint64_t)];
        //print("byte:", byte);
        *(uint8_t *)(func_addr + i) = byte;

    }
    
    #ifdef _WIN32
    free(RelocsInCurrentFunction);
    #endif
    #ifdef __linux__
    ModifyPagePermissionToOldProtect(func_addr, size, pflOldProtect);
    #endif
        
}


/// <summary>
/// Decrypt the specified dll/exe file
/// </summary>
/// <param name="BaseAddr"></param>
#ifdef _WIN32
static void DecryptSMCFile(UINT64 BaseAddr) {
    //print("DecryptSMCFile ing ", (int)BaseAddr);
    if (HasBeenDecrypted((ADDR)BaseAddr))
        return;
    GetSectionInfoInPE(BaseAddr);
    if (smc_start == nullptr)
      return;
  /*  if (RelocItems)
        free(RelocItems);*/
    GetRelocationInfoInPE(BaseAddr); 
    
    // After these two function, the global variable
    // smc_start\smc_end\rdata_start\rdata_end\text_start\text_end\RelocItems
    // will be set to  corresponding information of the given file

    // Modify PagePermission To Write&Read&Execution
    PDWORD pflOldProtect_text = ModifyPagePermissionToWRX(
        text_start + BaseAddr, text_end - text_start);


    PDWORD pflOldProtect_rdata =
        ModifyPagePermissionToWRX(rdata_start+BaseAddr, rdata_end - rdata_start);
    
    // Parse Each smcsec_entry
    // The format of smcsec is as follows:
    // smcsec_entry of funcs(64bit):
    // | func_start | func_end | reloc_start | reloc_end |
    // 0  - - - - 15 16 - -  31 32 - - - - 47 48 - - - 63
    // smcsec_entry of global variable(64bit):
    // | data_start | data_size | reloc_start | reloc_end |
    // 0  - - - - 15 16 - -  31 32 - - - - 47 48 - - - 63
    // func_start & func_end: the start addr and end addr of encrypted function
    // data_start: the start add of encrypted global variable
    // reloc_start & reloc_end: index(in RelocItems array) of the first and last
    // relocation items in the given region(func_start - func_end),
    long long count = 0;
    for (ADDR *iter = smc_start; iter < smc_end; iter += 4) {
      ADDR func_start = *iter;
      /*if (func_start == 0x0) {
        iter++;
        continue;
      }*/
      ADDR func_end = 0;
      
     
      if (func_start >= rdata_start+BaseAddr && func_start < rdata_end+BaseAddr) {
        // if this symbol is in rdata sec, the second item is size of this
        // symbol
        ADDR size = *(iter + 1);
        func_end = func_start + size;
      } else {
        func_end = *(iter + 1);
      }
      ADDR reloc_start = *(iter + 2);
      ADDR reloc_end = *(iter + 3);

      unsigned long size = func_end - func_start;
      count++;
      smc_decrypt(func_start, size, reloc_start, reloc_end, BaseAddr);
    }
    // Modify the PagePermission back
    if (pflOldProtect_text != NULL)
      ModifyPagePermissionToOldProtect(text_start + BaseAddr,
                                       text_end - text_start,
                                       pflOldProtect_text);
    if (pflOldProtect_rdata != NULL)
      ModifyPagePermissionToOldProtect(rdata_start+BaseAddr, rdata_end - rdata_start,
                                       pflOldProtect_rdata);
}
#endif





/// <summary>
/// smc_helper process logic for exe files
/// </summary>
#ifdef _WIN32
static void smc_helper_OnExe() { 
   // print("in smc_helper_OnExe", 0);
    bool hasbeendecrypted = HasBeenDecrypted((ADDR)&__ImageBase);
   // print("decrypted", xxxxxx);
    if (hasbeendecrypted) {
      //print("Has Been Decrypted", 0);
      return;
    }
        
    UINT64 *DllBaseAddr = GetAllModuleBase(); 

    for (int index = 0;; index++) {
        if (DllBaseAddr[index] == -1)
            break;
        ADDR BaseAddr = (ADDR)DllBaseAddr[index];
        DecryptSMCFile(BaseAddr);
    }
}
#endif

#ifdef __linux__
static void smc_helper_OnLinux() {
  smc_start = (ADDR *)&_smc_start;
  smc_end = (ADDR *)&_smc_end;
  rdata_start = (ADDR)&_rodata_start;
  rdata_end = (ADDR)&_rodata_end;
  if (smc_start == smc_end) {
    // No .smcsec Found
    return;
  }
  for (ADDR *iter = smc_start; iter < smc_end; iter += 4) {
    ADDR func_start = *iter;
    // printf("%#llx\n", func_start);
    if (func_start == 0x0) {
      iter++;
      continue;
    }
    ADDR func_end = 0;
    if (func_start >= rdata_start && func_start <= rdata_end) {
      // if this symbol is in rdata sec, the second item is size of this symbol
      ADDR size = *(iter + 1);
      func_end = func_start + size;
    } else {
      func_end = *(iter + 1);
    }
    ADDR reloc_start = *(iter + 2);
    ADDR reloc_end = *(iter + 3);

    unsigned long size = func_end - func_start;
    smc_decrypt(func_start, size, reloc_start, reloc_end,0);
  }

}
#endif


extern "C" {
//#ifdef _WIN32
//	__declspec(dllexport) 
//#endif
#ifdef __linux__
    __attribute__((visibility("default")))
#endif
	void smc_helper() {
        
        if (decrypted)   // Ensure that the logic of smc_helper is only executed once
            return;
#ifdef _WIN32
       
       smc_helper_OnExe();
      
#endif
            
        
#ifdef __linux__
        smc_helper_OnLinux();
    
#endif
       
        decrypted = true;
      
	}
}
