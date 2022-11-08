
#include <stdio.h>
#include <assert.h>
#ifdef _WIN32 // On Windows OS
#include<windows.h>
#include <tchar.h>
#endif

int in_seh = 0;
int seh_main_arrived = 0;
int count_seh = 500;
int set_count_seh = 0;

extern "C" {

#ifdef _WIN32
    /*
    ExceptionHandler
        Catch the exception and check Dr1-Dr3, if there is something in these regiters,
        it means someone is watching you, exit the program as soon as possible!
    */
	LONG WINAPI ExceptionHandler(PEXCEPTION_POINTERS exPtr) {
        if (exPtr->ExceptionRecord->ExceptionCode != EXCEPTION_ACCESS_VIOLATION) {
            return EXCEPTION_CONTINUE_SEARCH;
        }
        if (exPtr->ExceptionRecord->ExceptionCode == EXCEPTION_ACCESS_VIOLATION) {
          //
          // The instruction that caused the exception is 6 byte long (at least on
          // 32 Bit Windows, compare with recover-from-access-violation.objdump).
          // We increase the instruction pointer (EIP) by these 6 bytes so as
          // to recover from the violation...
          //
    #ifndef _WIN64  // On Win32 Platform
          exPtr->ContextRecord->Eip += 6;
    #endif // !_WIN64
    #ifdef _WIN64  // On Win64 Platform
          exPtr->ContextRecord->Rip += 6;
    #endif // _WIN64

            // If any of Dr0-Dr3 is set, then there is a memory breakpoint, exit the program.
            int res = exPtr->ContextRecord->Dr0 + exPtr->ContextRecord->Dr1 +
                      exPtr->ContextRecord->Dr2 + exPtr->ContextRecord->Dr3;

            if (res != 0) {
              const char *msg = "Memory BreakPoint Detected!";
             // printf("%s\n",msg);
              exit(10086);
            }

            const char *msg = "No Memory BreakPoint Detected!";
            //printf("%s\n", msg);
            //SetThreadContext(GetCurrentThread(), exPtr->ContextRecord);
        
            //return EXCEPTION_CONTINUE_SEARCH;
			return EXCEPTION_CONTINUE_EXECUTION;
        }
}
#endif // _WIN32

#ifdef _WIN32
	__declspec(dllexport) 
#endif // _WIN32
#ifdef __linux__
	__attribute__((visibility("default")))
#endif // __linux__
	void seh_set_main_arrived() { 
#ifdef _WIN32
		//printf("In seh_helper main arrived\n");
		if (seh_main_arrived == 0) {
			// Regist exception handling function
			AddVectoredExceptionHandler(1, ExceptionHandler);
			seh_main_arrived = 1;
		}
#endif // _WIN32
	}

#ifdef _WIN32
    __declspec(dllexport)
#endif
#ifdef __linux__
    __attribute__((visibility("default")))
#endif
	void seh_helper(int count) {
		if (in_seh || !seh_main_arrived) {
			return;
		}
		if (!set_count_seh) {
			count_seh = count;
			set_count_seh = 1;
		}
		in_seh = 1;
#ifdef _WIN32
		if (count_seh > 0) {
			// Trigger the exception in a stupid way
			//printf("In seh_helper\n");
			count_seh--;
			int *ptr;
			ptr = (int *)0;
			*ptr = 42;
		}
#endif // _WIN32
#ifdef __linux__
		assert("SEH is not supported for Linux");
#endif // __linux__
		in_seh = 0;
		//printf("In seh_helper!\n");
	}
}


