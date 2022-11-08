#pragma once
#include "FileParser.h"
#ifdef _WIN32
#include <Windows.h>


template <typename T>
struct RELOC_ITEM_T
{
    T RVA;
    T FOA;
    std::string type;
    std::string section;
};

typedef struct _SMCSEC_ENTRY64_T
{
    UINT64 func_start;
    UINT64 func_end;
    UINT64 reloc_start;
    UINT64 reloc_end;
} SMCSEC_ENTRY64_T;

typedef struct _SMCSEC_ENTRY32_T
{
    UINT32 func_start;
    UINT32 func_end;
    UINT32 reloc_start;
    UINT32 reloc_end;
} SMCSEC_ENTRY32_T;

class PEParser :public FileParser {
public:
    PEParser() = default;
    PEParser(std::string filepath) {
        FilePath = filepath;
        OpenFileByName();
        SetISA();
        GetImageBase();
    }
    void OpenFileByName() override;
    intptr_t GetImageBase() override;
    std::vector<std::pair<int, int>> GetEncryptFunctionInfo() override; 
    std::vector<std::set<int>> GetRelocationInfo() override;


private:
    PIMAGE_DOS_HEADER GetDosHeader();
    PIMAGE_NT_HEADERS32 GetNtHeader32();
    PIMAGE_NT_HEADERS64 GetNtHeader64();
    PIMAGE_FILE_HEADER GetFileHeader64();
    PIMAGE_FILE_HEADER GetFileHeader32();
    PIMAGE_OPTIONAL_HEADER32 GetOptionalHeader32();
    PIMAGE_OPTIONAL_HEADER64 GetOptionalHeader64();
    void SetISA();
    uint64_t RVAToFOA64(uint64_t address);
    uint32_t RVAToFOA32(uint32_t address);
    std::string GetSecNameOf64(uint64_t address);
    std::string GetSecNameOf32(uint32_t address);
    std::string GetRelocType(int tt);
    std::vector<RELOC_ITEM_T<uint64_t>> ParseRelocationTable64();
    std::vector<RELOC_ITEM_T<uint32_t>> ParseRelocationTable32();
    std::vector<SMCSEC_ENTRY64_T> GetEncryptFuncs64();
    std::vector<SMCSEC_ENTRY32_T> GetEncryptFuncs32();

};

#endif

