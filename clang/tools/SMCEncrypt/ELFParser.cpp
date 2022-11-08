
#include "ELFParser.h"
#ifdef __linux__
std::vector<section_t> ELFParser::Get_Sections64() {
    Elf64_Ehdr* ehdr = (Elf64_Ehdr*)m_mmap_program;

    Elf64_Shdr* shdr = (Elf64_Shdr*)(m_mmap_program + ehdr->e_shoff);
    int shnum = ehdr->e_shnum;

    Elf64_Shdr* sh_strtab = &shdr[ehdr->e_shstrndx];
    const char* const sh_strtab_p = (char*)m_mmap_program + sh_strtab->sh_offset;

    std::vector<section_t> sections;
    for (int i = 0; i < shnum; ++i) {
        section_t section;
        section.section_index = i;
        section.section_name = std::string(sh_strtab_p + shdr[i].sh_name);
        section.section_type = Get_Section_Type(shdr[i].sh_type);
        section.section_addr = shdr[i].sh_addr;
        section.section_offset = shdr[i].sh_offset;
        section.section_size = shdr[i].sh_size;
        section.section_ent_size = shdr[i].sh_entsize;
        section.section_addr_align = shdr[i].sh_addralign;

        sections.push_back(section);
    }
    return sections;
}

std::vector<section_t> ELFParser::Get_Sections32() {
    Elf32_Ehdr* ehdr = (Elf32_Ehdr*)m_mmap_program;

    Elf32_Shdr* shdr = (Elf32_Shdr*)(m_mmap_program + ehdr->e_shoff);
    int shnum = ehdr->e_shnum;

    Elf32_Shdr* sh_strtab = &shdr[ehdr->e_shstrndx];
    const char* const sh_strtab_p = (char*)m_mmap_program + sh_strtab->sh_offset;

    std::vector<section_t> sections;
    for (int i = 0; i < shnum; ++i) {
        section_t section;
        section.section_index = i;
        section.section_name = std::string(sh_strtab_p + shdr[i].sh_name);
        section.section_type = Get_Section_Type(shdr[i].sh_type);
        section.section_addr = shdr[i].sh_addr;
        section.section_offset = shdr[i].sh_offset;
        section.section_size = shdr[i].sh_size;
        section.section_ent_size = shdr[i].sh_entsize;
        section.section_addr_align = shdr[i].sh_addralign;

        sections.push_back(section);
    }
    return sections;
}





void ELFParser::OpenFileByName() {
    int fd, i;
    struct stat st;

    if ((fd = open(FilePath.c_str(), O_RDWR)) < 0) {
        printf("Err: open\n");
        exit(-1);
    }
    if (fstat(fd, &st) < 0) {
        printf("Err: fstat\n");
        exit(-1);
    }
    m_mmap_program = static_cast<uint8_t*>(mmap(NULL, st.st_size, PROT_READ | PROT_WRITE, MAP_SHARED, fd, 0));
    if (m_mmap_program == MAP_FAILED) {
        printf("Err: mmap\n");
        exit(-1);
    }

    //TODO Support 32-bit
    auto header = (Elf64_Ehdr*)m_mmap_program;
    if (header->e_ident[EI_CLASS] == ELFCLASS64) {
        ISA = X64;
    }else if(header->e_ident[EI_CLASS] == ELFCLASS32){
        ISA = X86;
    }
    BaseAddr = (intptr_t)m_mmap_program;
    //m_mmap_program = m_mmap_program;
}

std::string ELFParser::Get_Section_Type(int tt) {
    if (tt < 0)
        return "UNKNOWN";

    switch (tt) {
    case 0: return "SHT_NULL";      /* Section header table entry unused */
    case 1: return "SHT_PROGBITS";  /* Program data */
    case 2: return "SHT_SYMTAB";    /* Symbol table */
    case 3: return "SHT_STRTAB";    /* String table */
    case 4: return "SHT_RELA";      /* Relocation entries with addends */
    case 5: return "SHT_HASH";      /* Symbol hash table */
    case 6: return "SHT_DYNAMIC";   /* Dynamic linking information */
    case 7: return "SHT_NOTE";      /* Notes */
    case 8: return "SHT_NOBITS";    /* Program space with no data (bss) */
    case 9: return "SHT_REL";       /* Relocation entries, no addends */
    case 11: return "SHT_DYNSYM";   /* Dynamic linker symbol table */
    default: return "UNKNOWN";
    }
    return "UNKNOWN";
}

std::string ELFParser::Get_Symbol_Type(uint8_t& sym_type) {
    switch (ELF32_ST_TYPE(sym_type)) {
    case 0: return "NOTYPE";
    case 1: return "OBJECT";
    case 2: return "FUNC";
    case 3: return "SECTION";
    case 4: return "FILE";
    case 6: return "TLS";
    case 7: return "NUM";
    case 10: return "LOOS";
    case 12: return "HIOS";
    default: return "UNKNOWN";
    }
}

std::string ELFParser::Get_Symbol_Bind(uint8_t& sym_bind) {
    switch (ELF32_ST_BIND(sym_bind)) {
    case 0: return "LOCAL";
    case 1: return "GLOBAL";
    case 2: return "WEAK";
    case 3: return "NUM";
    case 10: return "UNIQUE";
    case 12: return "HIOS";
    case 13: return "LOPROC";
    default: return "UNKNOWN";
    }
}


std::string ELFParser::Get_Symbol_Visibility(uint8_t& sym_vis) {
    switch (ELF32_ST_VISIBILITY(sym_vis)) {
    case 0: return "DEFAULT";
    case 1: return "INTERNAL";
    case 2: return "HIDDEN";
    case 3: return "PROTECTED";
    default: return "UNKNOWN";
    }
}

std::string ELFParser::Get_Symbol_Index(uint16_t& sym_idx) {
    switch (sym_idx) {
    case SHN_ABS: return "ABS";
    case SHN_COMMON: return "COM";
    case SHN_UNDEF: return "UND";
    case SHN_XINDEX: return "COM";
    default: return std::to_string(sym_idx);
    }
}
intptr_t ELFParser::GetImageBase(){
    if(ISA == X64){
        return GetImageBase64();
    }else if(ISA == X86){
        return GetImageBase32();
    }
    return -1;
}

intptr_t ELFParser::GetImageBase64() {
    if (ImageBase != 0xffffffff) {                                                               // We have calculate ImageBase before
        return ImageBase;
    }
    Elf64_Ehdr* ehdr = (Elf64_Ehdr*)m_mmap_program;
    Elf64_Phdr* phdr = (Elf64_Phdr*)(m_mmap_program + ehdr->e_phoff);
    int phnum = ehdr->e_phnum;
    intptr_t load_base = INT64_MAX;
    for (int i = 0; i < phnum; ++i) {
        if (phdr[i].p_type == PT_LOAD) {
            if (phdr[i].p_vaddr < load_base)
                load_base = phdr[i].p_vaddr;
        }

    }
    ImageBase = load_base;
}

intptr_t ELFParser::GetImageBase32() {
    if (ImageBase != 0xffffffff) {                                                               // We have calculate ImageBase before
        return ImageBase;
    }
    Elf32_Ehdr* ehdr = (Elf32_Ehdr*)m_mmap_program;
    Elf32_Phdr* phdr = (Elf32_Phdr*)(m_mmap_program + ehdr->e_phoff);
    int phnum = ehdr->e_phnum;
    intptr_t load_base = INT64_MAX;
    for (int i = 0; i < phnum; ++i) {
        if (phdr[i].p_type == PT_LOAD) {
            if (phdr[i].p_vaddr < load_base)
                load_base = phdr[i].p_vaddr;
        }

    }
    ImageBase = load_base;
}

std::vector<std::pair<int,int>> ELFParser::GetEncryptFuncsFromSMCSection64(){
    std::vector<std::pair<int,int>> encrypt_funcs;
    std::vector<section_t> sections = Get_Sections64();
    uint64_t rodata_start = 0, rodata_end = 0;
    for(section_t s : sections){
        if(s.section_name == ".rodata"){
            rodata_start = s.section_offset;
            rodata_end = s.section_offset + s.section_size;
        }
        if(s.section_name == ".smcsec"){
            intptr_t ptr = s.section_offset;
            for(int i = 0; i<s.section_size; i+=32){
                //printf("BaseAddr: %#lx\n",BaseAddr);
                uint64_t func_start = Read_8Bytes((intptr_t)(m_mmap_program + ptr + i)) - GetImageBase();
                uint64_t func_end = 0 ;
                if( func_start >= rodata_start && func_start <= rodata_end){
                    uint64_t length = Read_8Bytes((intptr_t)(m_mmap_program + ptr + i + 8));
                    func_end = func_start + length;
                }else{
                    func_end = Read_8Bytes((intptr_t)(m_mmap_program + ptr + i + 8)) - GetImageBase();
                }
                intptr_t reloc_start = Read_8Bytes((intptr_t)(m_mmap_program + ptr + i + 16));
                if(reloc_start != 0x123456789abcdef){
                    break;
                }
                uint64_t size = func_end - func_start;
                encrypt_funcs.push_back(std::make_pair(func_start,size));
            }
        }
    }
    return encrypt_funcs;
}

std::vector<std::pair<int,int>> ELFParser::GetEncryptFuncsFromSMCSection32(){
    std::vector<std::pair<int,int>> encrypt_funcs;
    std::vector<section_t> sections = Get_Sections32();
    uint32_t rodata_start = 0, rodata_end = 0;
    for(section_t s : sections){
        if(s.section_name == ".rodata"){
            rodata_start = s.section_offset;
            rodata_end = s.section_offset + s.section_size;
            // printf("rodata_start: %d \n",rodata_start);
            // printf("rodata_end: %d \n",rodata_end);
        }
        if(s.section_name == ".smcsec"){
            intptr_t ptr = s.section_offset;
            for(int i = 0; i<s.section_size; i+=16){
                //printf("BaseAddr: %#lx\n",BaseAddr);
                int func_start = Read_4Bytes((intptr_t)(m_mmap_program + ptr + i)) - GetImageBase();
                uint32_t func_end = 0 ;
                if( func_start >= rodata_start && func_start <= rodata_end){
                    uint32_t length = Read_4Bytes((intptr_t)(m_mmap_program + ptr + i + 4));
                    func_end = func_start + length;
                }else{
                    func_end = Read_4Bytes((intptr_t)(m_mmap_program + ptr + i + 4)) - GetImageBase();
                }
                intptr_t reloc_start = Read_4Bytes((intptr_t)(m_mmap_program + ptr + i + 8));
                if(reloc_start != 0x12345678){
                    break;
                }
                int size = func_end - func_start;
                encrypt_funcs.push_back(std::make_pair(func_start,size));
            }
        }
    }
    return encrypt_funcs;
}

std::vector<std::pair<int, int>> ELFParser::GetEncryptFunctionInfo(){
    if(ISA == X64){
        return GetEncryptFuncsFromSMCSection64();
    }else if (ISA == X86){
        return GetEncryptFuncsFromSMCSection32();
    }
}

std::vector<std::set<int>> ELFParser::GetRelocationInfoFromSMCSection64(){
    std::vector<std::set<int>> Relocs;
    std::vector<section_t> sections = Get_Sections64();
    for(section_t s : sections){
        if(s.section_name == ".smcsec"){
            intptr_t ptr = s.section_offset;
            for(int i = 0; i<s.section_size; i+=32){
                std::set<int> reloc_item;
                unsigned long func_start = Read_8Bytes((intptr_t)(m_mmap_program + ptr + i)) - GetImageBase();
                //printf("func_start: %#lx\n",func_start);
                unsigned long func_end = Read_8Bytes((intptr_t)(m_mmap_program + ptr + i + 8)) - GetImageBase();
                unsigned long reloc_start = Read_8Bytes((intptr_t)(m_mmap_program + ptr + i + 16));
                if(reloc_start != 0x123456789abcdef){
                    break;
                }
                Modify_8Bytes((intptr_t)(m_mmap_program + ptr + i + 16), -1);
                Modify_8Bytes((intptr_t)(m_mmap_program + ptr + i + 24), -1);
                unsigned long size = func_end - func_start;
                Relocs.push_back(reloc_item);
            }
        }
    }
    return Relocs;
}
std::vector<std::set<int>> ELFParser::GetRelocationInfoFromSMCSection32(){
    std::vector<std::set<int>> Relocs;
    std::vector<section_t> sections = Get_Sections32();
    for(section_t s : sections){
        if(s.section_name == ".smcsec"){
            intptr_t ptr = s.section_offset;
            for(int i = 0; i<s.section_size; i+=16){
                std::set<int> reloc_item;
                unsigned long func_start = Read_4Bytes((intptr_t)(m_mmap_program + ptr + i)) - GetImageBase();
                //printf("func_start: %#lx\n",func_start);
                unsigned long func_end = Read_4Bytes((intptr_t)(m_mmap_program + ptr + i + 4)) - GetImageBase();
                unsigned long reloc_start = Read_4Bytes((intptr_t)(m_mmap_program + ptr + i + 8));
                if(reloc_start != 0x12345678){
                    break;
                }
                Modify_4Bytes((intptr_t)(m_mmap_program + ptr + i + 8), -1);
                Modify_4Bytes((intptr_t)(m_mmap_program + ptr + i + 12), -1);
                unsigned long size = func_end - func_start;
                Relocs.push_back(reloc_item);
            }
        }
    }
    return Relocs;
}

std::vector<std::set<int>> ELFParser::GetRelocationInfo(){
    // std::cout<<"ISA: "<<ISA<<std::endl;
    if(ISA == X64){
        return GetRelocationInfoFromSMCSection64();
    }else if(ISA == X86){
        return GetRelocationInfoFromSMCSection32();
    }
    
}


#endif