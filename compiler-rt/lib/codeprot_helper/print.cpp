#include <stdio.h>

extern "C" {
#ifdef _WIN32
	__declspec(dllexport) 
#endif
#ifdef __linux__
    __attribute__((visibility("default")))
#endif
	void print(char * info) {
		printf("%s\n", info);
	}
}
