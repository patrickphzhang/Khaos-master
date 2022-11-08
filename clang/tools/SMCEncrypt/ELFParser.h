#pragma once
#ifdef __linux__
#include <fcntl.h>    /* O_RDONLY */
#include "FileParser.h"
#include <sys/stat.h> /* For the size of the file. , fstat */
#include <sys/mman.h> /* mmap, MAP_PRIVATE */
#include <elf.h>      // Elf64_Shdr

typedef struct {
    int section_index = 0;
    std::intptr_t section_offset, section_addr;
    std::string section_name;
    std::string section_type;
    int section_size, section_ent_size, section_addr_align;
} section_t;

typedef struct {
    std::string symbol_index;
    std::intptr_t symbol_value;
    Elf64_Sym* sym;
    int symbol_num = 0, symbol_size = 0;
    std::string symbol_type, symbol_bind, symbol_visibility, symbol_name, symbol_section;
} symbol_t;

class ELFParser : public FileParser {
public:
    ELFParser() = default;
    ELFParser(std::string filepath) {
        FilePath = filepath;
        OpenFileByName();
        GetImageBase();
    }
    void OpenFileByName() override;
    intptr_t GetImageBase() override;
    std::vector<std::pair<int, int>> GetEncryptFunctionInfo() override;
    std::vector<std::set<int>> GetRelocationInfo() override;



private:
    uint8_t *m_mmap_program;
    intptr_t GetImageBase64();
    intptr_t GetImageBase32();
    std::vector<section_t> Get_Sections64();
    std::vector<section_t> Get_Sections32();
    std::vector<std::pair<int, int>> GetEncryptFuncsFromSMCSection64();
    std::vector<std::pair<int, int>> GetEncryptFuncsFromSMCSection32();
    std::vector<std::set<int>> GetRelocationInfoFromSMCSection64();
    std::vector<std::set<int>> GetRelocationInfoFromSMCSection32();
    std::string Get_Section_Type(int tt);
    std::string Get_Symbol_Type(uint8_t& sym_type);
    std::string Get_Symbol_Bind(uint8_t &sym_bind);
    std::string Get_Symbol_Visibility(uint8_t& sym_vis);
    std::string Get_Symbol_Index(uint16_t& sym_idx);
};

#endif