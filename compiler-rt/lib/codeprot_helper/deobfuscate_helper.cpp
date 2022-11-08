#include <stdio.h>
#include <stdint.h>

unsigned long long PayloadKey = 0x0;
bool deobfuscated = false;

#ifdef __linux__
const void *_payload_start;
const void *_payload_end;
#if defined(__x86_64__)
typedef unsigned long long ADDR;
#else
typedef unsigned long ADDR;
#endif
#endif //__linux__

#ifdef _WIN32
#include <windows.h>
#include <tchar.h>
extern "C" const IMAGE_DOS_HEADER __ImageBase;
#if defined(_WIN64)
typedef unsigned long long ADDR;
#else
typedef unsigned long ADDR;
#endif
ADDR res[2];
void parsepe();
#endif // _WIN32

extern "C" {
#ifdef _WIN32
	__declspec(dllexport) 
#endif
#ifdef __linux__
    __attribute__((visibility("default")))
#endif
	void deobfuscate_helper() {
		//printf("In deobfuscate_helper!\n");
		if (!PayloadKey || deobfuscated)
		{
			//printf("No PayloadKey!\n");
			return;
		}
		//printf("PayloadKey: 0x%llx\n", PayloadKey);
		ADDR *payload_start, *payload_end;
		#ifdef __linux__
		payload_start = (ADDR*)&_payload_start;
		payload_end = (ADDR*)&_payload_end;
		#endif

		#ifdef _WIN32
		parsepe();
		payload_start = (ADDR*)res[0];
		payload_end = (ADDR*)res[1];
		#endif
		//printf("res[0]: 0x%llx\n", res[0]);
		//printf("res[1]: 0x%llx\n", res[1]);
		//printf("payload start: %p\n", payload_start);
		//printf("payload end: %p\n", payload_end);
		// deobfuscate
		// Payload key is an unsigned long long, which can split to four child keys
		// | 63 - 48 | 47 - 32 | 31 - 16 | 15 - 0 |
		// Every child key is an unsigned short, which is used to deobfuscate a quad
		// The highest bit indicates the quad should plus or minus a random number
		// The lower 15 bits is the random number
		// eg. 0x1234, aka, 0001 0010 0011 0100
		// means            +001 0010 0011 0100
		unsigned short key[4] = {(unsigned short)PayloadKey, (unsigned short)(PayloadKey >> 16),
								(unsigned short)(PayloadKey >> 32), (unsigned short)(PayloadKey >> 48)};
		for (ADDR *iter = payload_start, i = 0; iter < payload_end; iter++, i++)
		{
			//printf("iter: %p\n", iter);
			//printf("befor deobfuscate: %p\n", *iter);
			unsigned short k = key[i % 4];
			//printf("key: %u\n", k);
			if (k & 0x8000)
				*iter -= k & 0x7fff;
			else
				*iter += k & 0x7fff;
			//printf("after deobfuscate: %p\n", *iter);
		}
        deobfuscated = true;
	}
}

#ifdef _WIN32
void parsepe() {
	//ADDR res[2];
	//HMODULE hModule = GetModuleHandle(NULL);
	//_tprintf(TEXT("with GetModuleHandle(NULL) = 0x%x\r\n"), hModule);
	//_tprintf(TEXT("with __ImageBase = 0x%x\r\n"), (HINSTANCE)&__ImageBase);
	//hModule = NULL;
	//GetModuleHandleEx(GET_MODULE_HANDLE_EX_FLAG_FROM_ADDRESS, (PCTSTR)parsepe, &hModule);
	//_tprintf(TEXT("with GetModuleHandleEx = 0x%x\r\n"), hModule);

	ADDR lpMapAddr = (ADDR)&__ImageBase;
	PIMAGE_DOS_HEADER pDosHeader = (PIMAGE_DOS_HEADER)lpMapAddr;
	PIMAGE_NT_HEADERS pNtHeader = (PIMAGE_NT_HEADERS)(pDosHeader->e_lfanew + lpMapAddr);
	PIMAGE_FILE_HEADER pFileHeader = (PIMAGE_FILE_HEADER)&(pNtHeader->FileHeader);
	PIMAGE_SECTION_HEADER pFirstSectionHeader = IMAGE_FIRST_SECTION(pNtHeader);
	for (int i = 0; i < pFileHeader->NumberOfSections; i++) {
		PIMAGE_SECTION_HEADER pSectionHeader = (PIMAGE_SECTION_HEADER)((ADDR)pFirstSectionHeader + i * IMAGE_SIZEOF_SECTION_HEADER);
		//printf("%s\n", (const char*)(pSectionHeader->Name));
		if (strstr((const char*)(pSectionHeader->Name), ".payload")) {
			//printf("lpMapAddr: 0x%llx\n", lpMapAddr);
			ADDR payloadStart = pSectionHeader->VirtualAddress + lpMapAddr;
			ADDR payloadEnd = pSectionHeader->Misc.VirtualSize + payloadStart;
			//printf("Payload Start: 0x%llx\n", payloadStart);
			//printf("Payload End: 0x%llx\n", payloadEnd);
			res[0] = payloadStart;
			res[1] = payloadEnd;
			break;
		}
	}

	//return res;
}
#endif