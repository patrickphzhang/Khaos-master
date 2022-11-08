#include <stdio.h>

#ifdef _WIN32
#include <windows.h>
#endif // WIN32
extern "C" {
#ifdef _WIN32
	__declspec(dllexport) 
#endif
#ifdef __linux__
    __attribute__((visibility("default")))
#endif
	void antidump_helper() {

#ifdef _WIN32
	/* Make the PE header unaccessable  */
	DWORD dwOldProtect;
	HMODULE ImageBase = GetModuleHandle(NULL);
	VirtualProtect(ImageBase, 1000, PAGE_NOACCESS, &dwOldProtect);
#endif // _WIN32
    //printf("In antidump_helper!\n");
  
	}
}




