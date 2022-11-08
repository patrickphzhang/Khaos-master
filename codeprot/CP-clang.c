#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#ifdef __linux__
#include <unistd.h>
#include <sys/time.h>
#include <sys/types.h>
#include <sys/stat.h>
#endif
#ifdef _WIN32
#include <process.h>
#include <errno.h>
#include <direct.h>
#include <Windows.h>
#endif // _WIN32

typedef unsigned char u8;
typedef unsigned int u32;
typedef unsigned long u64;
typedef unsigned long ADDR;

// cc_params: array to contain params for clang/clang-cl.
static u8 **cc_params = NULL;
// cc_par_cnt: total count of params in cc_params.
static u32 cc_par_cnt = 0;
// smc_params: array to contain params for SMCEncrypt.
static u8 **smc_params;
// smc_par_cnt: total count of params in smc_params.
static u32 smc_par_cnt = 0;
// strip_params: array to contain params for strip.
static u8 **strip_params;
// strip_par_cnt: total count of params in strip_params.
static u32 strip_par_cnt = 0;
// Path for clang/clang-cl, smc and strip.
static u8 *cc_path = NULL;
static u8 *smc_path = NULL;
static u8 *strip_path = NULL;
static u8 *resource_path = NULL;
// Path for ld_script.
static u8 *ld_script_path = NULL;

static u8 *out_path = NULL;

static u8 smc_flag = 0;
static u8 special_flag = 0;
static u8 symobf_flag = 0;

static void edit_params(int argc, char** argv) {


}

void get_time_start(u64 *time_hi, u64 *time_lo) {

    //printf("current_time_low = %uld\n", *time_lo);
}

void get_time_end(u64 *time_hi, u64 *time_lo, u8 *path) {

}

int main(int argc, char** argv) {
    return 0;
}