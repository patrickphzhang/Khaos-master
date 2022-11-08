#ifdef _WIN32
#include <stdio.h>
#include <windows.h>
extern "C" const IMAGE_DOS_HEADER __ImageBase;

// avoid recursive call
// because we use some library functions like puts
// if one of these functions is protected by pageguard
// recursive call would happen
int in_page_guard = 0;
int main_arrived = 0;
int count_page_guard = 500;
int set_count_page_guard = 0;
unsigned long text_base_addr = 0, text_size = 0, 
              data_base_addr = 0, data_size = 0, 
              rdata_base_addr = 0, rdata_size = 0;
typedef DWORD ADDR;
extern "C" {
#ifndef _WIN64
/* Read the addr and test access time.
 */
UINT64 get_access_time(unsigned long addr) {
    unsigned int time_begin_h = 0, time_end_h = 0,
        time_begin_l = 0, time_end_l = 0;
    __asm
        {
				pusha // Save all General-Purpose Registers
				mov eax, addr
				mov ebx, [eax] // Read addr to cache, to get accurate time later
				cpuid // Make sure instructions above is finished
				rdtscp // time start          
				mov time_begin_l, eax
				mov time_begin_h, edx
				mov eax, addr         
				mov ebx, [eax] // perform the read
				rdtscp // time end
				mov time_end_l, eax
				mov time_end_h, edx
				popa
        }
    UINT64 time_begin = 0, time_end = 0, temp = 0;
    temp = time_begin_h;
    time_begin = (temp << 32) | time_begin_l;
    temp = time_end_h;
    time_end = (temp << 32) | time_end_l;
    //printf("Access time: %lld!\n", time_end - time_begin);
    return time_end - time_begin;
}

void read_test(unsigned long addr, UINT64 threshold) {
    // we try 100 times, if every time the access time is larger than threshold, report
  int count = 0;
  while (get_access_time(addr) > threshold && ++count < 100)
    ;

  if (count == 100) {
   // printf("Memory BreakPoint Detected!\n");
    exit(10086);
  }
}

/* Implement page guard protect to .text section, .data section and .rdata section
 */
void protect_data_section(UINT64 threshold) {
    unsigned int num = text_size / 0x1000; // num of pages
    // printf("total %d data pages: \n", num);
    // read each page
    for (unsigned i = 0; i < num; i++) {
      // printf("testing %d data page: \n", i);
      read_test(text_base_addr + i * 0x1000, threshold);
    }
    num = data_size / 0x1000; // num of pages
    //printf("total %d data pages: \n", num);
    // read each page
    for (unsigned i = 0; i < num; i++) {
      //printf("testing %d data page: \n", i);
      read_test(data_base_addr + i * 0x1000, threshold);
    }
    num = rdata_size / 0x1000; // num of pages
    //printf("total %d rdata pages: \n", num);
    // read each page
    for (unsigned i = 0; i < num; i++) {
      //printf("testing %d rdata page: \n", i);
      read_test(rdata_base_addr + i * 0x1000, threshold);
    }
  // return res;
}

#endif // !_WIN64

__declspec(dllexport) void pageguard_set_main_arrived() { 
#ifndef _WIN64
  if (main_arrived)
    return;
  main_arrived = 1; 
  ADDR lpMapAddr = (ADDR)&__ImageBase;
  PIMAGE_DOS_HEADER pDosHeader = (PIMAGE_DOS_HEADER)lpMapAddr;
  PIMAGE_NT_HEADERS pNtHeader =
      (PIMAGE_NT_HEADERS)(pDosHeader->e_lfanew + lpMapAddr);
  PIMAGE_FILE_HEADER pFileHeader =
      (PIMAGE_FILE_HEADER) & (pNtHeader->FileHeader);
  PIMAGE_SECTION_HEADER pFirstSectionHeader = IMAGE_FIRST_SECTION(pNtHeader);
  for (int i = 0; i < pFileHeader->NumberOfSections; i++) {
    PIMAGE_SECTION_HEADER pSectionHeader = (PIMAGE_SECTION_HEADER)(
        (ADDR)pFirstSectionHeader + i * IMAGE_SIZEOF_SECTION_HEADER);
    
    if (strstr((const char *)(pSectionHeader->Name), ".text")) {
      text_base_addr = pSectionHeader->VirtualAddress + lpMapAddr;
      text_size = pSectionHeader->Misc.VirtualSize;
    }
    if (strstr((const char *)(pSectionHeader->Name), ".data")) {
      data_base_addr = pSectionHeader->VirtualAddress + lpMapAddr;
      data_size = pSectionHeader->Misc.VirtualSize;
    }
    if (strstr((const char *)(pSectionHeader->Name), ".rdata")) {
      rdata_base_addr = pSectionHeader->VirtualAddress + lpMapAddr;
      rdata_size = pSectionHeader->Misc.VirtualSize;
    }
  }
    protect_data_section(10000);
#endif
}

__declspec(dllexport) int pageguard_helper(unsigned long long addr, int count) {
#ifndef _WIN64
	if (in_page_guard || !main_arrived) {
		return 0;
	}
	if (!set_count_page_guard) {
		count_page_guard = count;
		set_count_page_guard = 1;
	}
	in_page_guard = 1;
	if (count_page_guard > 0) {
		UINT64 threshold = 10000; // TODO: get threshold dynamically (ZK)
		//printf("In pageguard_helper WIN32!\n");
		//printf("addr is %llx\n", addr);
		read_test(addr, threshold);
		protect_data_section(threshold);
		count_page_guard--;
	}
	in_page_guard = 0;

#endif // !_WIN64
	return 0;
}

} // end extern "C"
#endif