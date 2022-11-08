#include "PEParser.h"
#ifdef _WIN32

void PEParser::OpenFileByName() {
  LPCSTR peFile = (LPCSTR)FilePath.c_str();
  HANDLE hFile, hMapFile, lpMapAddress = NULL;
  DWORD dwFileSize = 0;

  hFile = CreateFileA(peFile, GENERIC_WRITE | GENERIC_READ, 0, NULL,
                      OPEN_EXISTING, FILE_ATTRIBUTE_NORMAL, NULL);
  if (hFile == INVALID_HANDLE_VALUE) {
    std::cout << "[ERROR] Open File Failed!" << std::endl;
    exit(-1);
  }
  dwFileSize = GetFileSize(hFile, NULL);
  hMapFile =
      CreateFileMappingA(hFile, NULL, PAGE_READWRITE, 0, dwFileSize, NULL);
  lpMapAddress = MapViewOfFile(hMapFile, FILE_MAP_ALL_ACCESS, 0, 0, dwFileSize);
  if (lpMapAddress != NULL) {
    BaseAddr = (intptr_t)lpMapAddress;
  }
}

PIMAGE_DOS_HEADER PEParser::GetDosHeader() {
  PIMAGE_DOS_HEADER pDosHeader = NULL;
  pDosHeader = (PIMAGE_DOS_HEADER)BaseAddr;
  return pDosHeader;
}

PIMAGE_NT_HEADERS32 PEParser::GetNtHeader32() {
  PIMAGE_DOS_HEADER pDosHeader = NULL;
  PIMAGE_NT_HEADERS32 pNtHeader = NULL;
  pDosHeader = GetDosHeader();
  pNtHeader =
      (IMAGE_NT_HEADERS32 *)((UINT64)pDosHeader + (UINT64)pDosHeader->e_lfanew);
  return pNtHeader;
}

PIMAGE_NT_HEADERS64 PEParser::GetNtHeader64() {
  PIMAGE_DOS_HEADER pDosHeader = NULL;
  PIMAGE_NT_HEADERS64 pNtHeader = NULL;
  pDosHeader = GetDosHeader();
  pNtHeader =
      (IMAGE_NT_HEADERS64 *)((UINT64)pDosHeader + (UINT64)pDosHeader->e_lfanew);
  return pNtHeader;
}

PIMAGE_FILE_HEADER PEParser::GetFileHeader32() {
  PIMAGE_NT_HEADERS32 pNtHeader = NULL;
  PIMAGE_FILE_HEADER pFileHeader = NULL;
  pNtHeader = GetNtHeader32();
  pFileHeader = &pNtHeader->FileHeader;
  return pFileHeader;
}

PIMAGE_FILE_HEADER PEParser::GetFileHeader64() {
  PIMAGE_NT_HEADERS64 pNtHeader = NULL;
  PIMAGE_FILE_HEADER pFileHeader = NULL;
  pNtHeader = GetNtHeader64();
  pFileHeader = &pNtHeader->FileHeader;
  return pFileHeader;
}

PIMAGE_OPTIONAL_HEADER32 PEParser::GetOptionalHeader32() {
  PIMAGE_NT_HEADERS32 pNtHead = NULL;
  PIMAGE_OPTIONAL_HEADER32 pOptinalHeader = NULL;
  pNtHead = GetNtHeader32();
  pOptinalHeader = &pNtHead->OptionalHeader;
  return pOptinalHeader;
}

PIMAGE_OPTIONAL_HEADER64 PEParser::GetOptionalHeader64() {
  PIMAGE_NT_HEADERS64 pNtHead = NULL;
  PIMAGE_OPTIONAL_HEADER64 pOptinalHeader = NULL;
  pNtHead = GetNtHeader64();
  pOptinalHeader = &pNtHead->OptionalHeader;
  return pOptinalHeader;
}

void PEParser::SetISA() { // Get file's ISA(x86\x64), must be excuted when
                          // initialize
  PIMAGE_FILE_HEADER pFileHead = GetFileHeader64();
  switch (pFileHead->Machine) {
  case 0x014c:
    ISA = X86;
    break;
  case 0x8664:
    ISA = X64;
    break;
  case 0x0200:
    ISA = IA64;
    break;
  default:
    ISA = UNKNOWN;
    break;
  }
}

intptr_t PEParser::GetImageBase() {
  if (ImageBase != 0xffffffff) { // We have calculate ImageBase before
    return ImageBase;
  }
  if (ISA == X86) { // 32 bit
    PIMAGE_OPTIONAL_HEADER32 pOptionalHeader = GetOptionalHeader32();
    ImageBase = pOptionalHeader->ImageBase;
  } else if (ISA == X64) {
    PIMAGE_OPTIONAL_HEADER64 pOptionalHeader = GetOptionalHeader64();
    ImageBase = pOptionalHeader->ImageBase;
  } // 64bit
}

uint64_t PEParser::RVAToFOA64(uint64_t address) {
  PIMAGE_OPTIONAL_HEADER64 pOptionalHeader = GetOptionalHeader64();
  PIMAGE_FILE_HEADER pFileHeader = GetFileHeader64();
  PIMAGE_SECTION_HEADER pSectionHeader[10];
  pSectionHeader[0] = (PIMAGE_SECTION_HEADER)((UINT64)(pOptionalHeader) +
                                              sizeof(IMAGE_OPTIONAL_HEADER64));
  for (int i = 0; i < pFileHeader->NumberOfSections - 1; i++) {
    pSectionHeader[i + 1] = (PIMAGE_SECTION_HEADER)(
        (UINT64)(pSectionHeader[i]) + IMAGE_SIZEOF_SECTION_HEADER);
  }
  int i = 0;
  for (; i < pFileHeader->NumberOfSections - 1; i++) {
    if (address >= pSectionHeader[i]->VirtualAddress &&
        address < pSectionHeader[i + 1]->VirtualAddress) {
      return address - pSectionHeader[i]->VirtualAddress +
             pSectionHeader[i]->PointerToRawData;
    }
  }
  if (i + 1 == pFileHeader->NumberOfSections) {
    return address - pSectionHeader[i]->VirtualAddress +
           pSectionHeader[i]->PointerToRawData;
  }
}

uint32_t PEParser::RVAToFOA32(uint32_t address) {
  PIMAGE_OPTIONAL_HEADER32 pOptionalHeader = GetOptionalHeader32();
  PIMAGE_FILE_HEADER pFileHeader = GetFileHeader32();
  PIMAGE_SECTION_HEADER pSectionHeader[10];
  pSectionHeader[0] = (PIMAGE_SECTION_HEADER)((UINT64)(pOptionalHeader) +
                                              sizeof(IMAGE_OPTIONAL_HEADER32));
  for (int i = 0; i < pFileHeader->NumberOfSections - 1; i++) {
    pSectionHeader[i + 1] = (PIMAGE_SECTION_HEADER)(
        (UINT64)(pSectionHeader[i]) + IMAGE_SIZEOF_SECTION_HEADER);
  }
  int i = 0;
  for (; i < pFileHeader->NumberOfSections - 1; i++) {
    if (address >= pSectionHeader[i]->VirtualAddress &&
        address < pSectionHeader[i + 1]->VirtualAddress) {
      return address - pSectionHeader[i]->VirtualAddress +
             pSectionHeader[i]->PointerToRawData;
    }
  }
  if (i + 1 == pFileHeader->NumberOfSections) {
    return address - pSectionHeader[i]->VirtualAddress +
           pSectionHeader[i]->PointerToRawData;
  }
}

std::string PEParser::GetSecNameOf64(uint64_t address) {
  PIMAGE_OPTIONAL_HEADER64 pOptionalHeader = GetOptionalHeader64();
  PIMAGE_FILE_HEADER pFileHeader = GetFileHeader64();
  PIMAGE_SECTION_HEADER pSectionHeader[10];
  pSectionHeader[0] = (PIMAGE_SECTION_HEADER)((UINT64)(pOptionalHeader) +
                                              sizeof(IMAGE_OPTIONAL_HEADER64));
  for (int i = 0; i < pFileHeader->NumberOfSections - 1; i++) {
    pSectionHeader[i + 1] = (PIMAGE_SECTION_HEADER)(
        (UINT64)(pSectionHeader[i]) + IMAGE_SIZEOF_SECTION_HEADER);
  }
  int i = 0;
  for (; i < pFileHeader->NumberOfSections - 1; i++) {
    if (address >= pSectionHeader[i]->VirtualAddress &&
        address < pSectionHeader[i + 1]->VirtualAddress) {
      std::string str;
      for (auto item : pSectionHeader[i]->Name) {
        // printf("%c ", item);
        str.push_back(item);
      }
      return str;
    }
  }
  if (i + 1 == pFileHeader->NumberOfSections) {
    std::string str;
    for (auto item : pSectionHeader[i]->Name) {
      str.push_back(item);
    }
    return str;
  }
}

std::string PEParser::GetSecNameOf32(uint32_t address) {
  PIMAGE_OPTIONAL_HEADER32 pOptionalHeader = GetOptionalHeader32();
  PIMAGE_FILE_HEADER pFileHeader = GetFileHeader32();
  PIMAGE_SECTION_HEADER pSectionHeader[10];
  pSectionHeader[0] = (PIMAGE_SECTION_HEADER)((UINT64)(pOptionalHeader) +
                                              sizeof(IMAGE_OPTIONAL_HEADER32));
  for (int i = 0; i < pFileHeader->NumberOfSections - 1; i++) {
    pSectionHeader[i + 1] = (PIMAGE_SECTION_HEADER)(
        (UINT64)(pSectionHeader[i]) + IMAGE_SIZEOF_SECTION_HEADER);
  }
  int i = 0;
  for (; i < pFileHeader->NumberOfSections - 1; i++) {
    if (address >= pSectionHeader[i]->VirtualAddress &&
        address < pSectionHeader[i + 1]->VirtualAddress) {
      std::string str;
      for (auto item : pSectionHeader[i]->Name) {
        // printf("%c ", item);
        str.push_back(item);
      }
      return str;
    }
  }
  if (i + 1 == pFileHeader->NumberOfSections) {
    std::string str;
    for (auto item : pSectionHeader[i]->Name) {
      str.push_back(item);
    }
    return str;
  }
}

std::string PEParser::GetRelocType(int tt) {
  if (tt < 0 && tt > 10)
    return "UNKNOWN";
  switch (tt) {
  case 0:
    return "ABSOLUTE"; // No relocation operation
  case 1:
    return "HIGH"; // The high 2 bytes of the relocation point need to be
                   // corrected
  case 2:
    return "LOW"; // The low 2 bytes of the relocation point need to be
                  // corrected
  case 3:
    return "HIGHLOW"; // All 4 bytes of the relocation point need to be
                      // corrected

  case 4:
    return "HIGHADJ"; // Very Complicated , I tried to understand it but failed
                      // , But it seems that such relocation type rarely appear
                      // (we haven't found it until now) We will try to solve it
                      // later when we meet one
  case 5:
    return "MACHINE_SPECIFIC_5";
  case 6:
    return "RESERVED";
  case 7:
    return "MACHINE_SPECIFIC_7";
  case 8:
    return "MACHINE_SPECIFIC_8";
  case 9:
    return "MACHINE_SPECIFIC_9";
  case 10:
    return "DIR64"; // The 8 bytes pointed to by the relocation need to be
                    // corrected
  default:
    return "UNKNOWN";
  }
}

std::vector<RELOC_ITEM_T<uint64_t>> PEParser::ParseRelocationTable64() {
  PIMAGE_DOS_HEADER pDosHeader = GetDosHeader();
  PIMAGE_FILE_HEADER pFileHead = GetFileHeader64();
  PIMAGE_OPTIONAL_HEADER64 pOptionHeader = GetOptionalHeader64();
  PIMAGE_DATA_DIRECTORY pDataDirectory = pOptionHeader->DataDirectory;
  PIMAGE_BASE_RELOCATION pBaseRelocation = (PIMAGE_BASE_RELOCATION)(
      (UINT64)pDosHeader + RVAToFOA64(pDataDirectory[5].VirtualAddress));
  UINT64 Size = 0;
  std::vector<RELOC_ITEM_T<UINT64>> relocs;
  while (Size < pDataDirectory[5].Size) {
    PWORD pRelocation =
        (PWORD)((UINT64)pBaseRelocation + sizeof(IMAGE_BASE_RELOCATION));
    DWORD NumberOfRelocationAddress =
        (pBaseRelocation->SizeOfBlock - sizeof(IMAGE_BASE_RELOCATION)) / 2;
    for (unsigned int i = NumberOfRelocationAddress; i > 0;
         pRelocation++, i--) // pRelocation++遍历重定位表中的地址表
    {
      RELOC_ITEM_T<UINT64> reloc_item;
      UINT64 RVA = (*pRelocation & 0xfff) | pBaseRelocation->VirtualAddress;
      reloc_item.RVA = RVA;
      reloc_item.type = GetRelocType((*pRelocation & 0xf000) >> 12);
      UINT64 FOA = RVAToFOA64(RVA);
      reloc_item.FOA = FOA;
      reloc_item.section = GetSecNameOf64(RVA);
      // std::cout << std::hex << reloc_item.FOA << "  " << reloc_item.RVA << "
      // " << reloc_item.section << "  " << reloc_item.type << std::endl;
      relocs.push_back(reloc_item);
    }
    Size += pBaseRelocation->SizeOfBlock;

    pBaseRelocation = (PIMAGE_BASE_RELOCATION)((UINT64)pBaseRelocation +
                                               pBaseRelocation->SizeOfBlock);
  }
  return relocs;
}

std::vector<RELOC_ITEM_T<UINT32>> PEParser::ParseRelocationTable32() {
  PIMAGE_DOS_HEADER pDosHeader = GetDosHeader();
  PIMAGE_FILE_HEADER pFileHead = GetFileHeader32();
  PIMAGE_OPTIONAL_HEADER32 pOptionHeader = GetOptionalHeader32();
  PIMAGE_DATA_DIRECTORY pDataDirectory = pOptionHeader->DataDirectory;
  PIMAGE_BASE_RELOCATION pBaseRelocation = (PIMAGE_BASE_RELOCATION)(
      (UINT64)pDosHeader + RVAToFOA32(pDataDirectory[5].VirtualAddress));
  UINT32 Size = 0;
  std::vector<RELOC_ITEM_T<UINT32>> relocs;
  while (pBaseRelocation->SizeOfBlock && pBaseRelocation->VirtualAddress) {
    PWORD pRelocation =
        (PWORD)((UINT64)pBaseRelocation + sizeof(IMAGE_BASE_RELOCATION));
    DWORD NumberOfRelocationAddress =
        (pBaseRelocation->SizeOfBlock - sizeof(IMAGE_BASE_RELOCATION)) / 2;
    for (unsigned int i = NumberOfRelocationAddress; i > 0;
         pRelocation++, i--) // pRelocation++遍历重定位表中的地址表
    {
      RELOC_ITEM_T<UINT32> reloc_item;
      UINT32 RVA = (*pRelocation & 0xfff) | pBaseRelocation->VirtualAddress;
      reloc_item.RVA = RVA;
      reloc_item.type = GetRelocType((*pRelocation & 0xf000) >> 12);
      UINT32 FOA = RVAToFOA32(RVA);
      reloc_item.FOA = FOA;
      reloc_item.section = GetSecNameOf32(RVA);
      // std::cout << std::hex << reloc_item.FOA << "  " << reloc_item.RVA << "
      // " << reloc_item.section << "  " << reloc_item.type << std::endl;
      relocs.push_back(reloc_item);
    }
    Size += pBaseRelocation->SizeOfBlock;

    pBaseRelocation = (PIMAGE_BASE_RELOCATION)((UINT64)pBaseRelocation +
                                               pBaseRelocation->SizeOfBlock);
  }
  return relocs;
}

std::vector<SMCSEC_ENTRY64_T> PEParser::GetEncryptFuncs64() {
  PIMAGE_OPTIONAL_HEADER64 pOptionalHeader = GetOptionalHeader64();
  PIMAGE_FILE_HEADER pFileHeader = GetFileHeader64();
  PIMAGE_SECTION_HEADER pSectionHeader[10];
  pSectionHeader[0] = (PIMAGE_SECTION_HEADER)((UINT64)(pOptionalHeader) +
                                              sizeof(IMAGE_OPTIONAL_HEADER64));

  std::vector<SMCSEC_ENTRY64_T> encrypt_funcs;
  for (int i = 0; i < pFileHeader->NumberOfSections - 1; i++) {
    pSectionHeader[i + 1] = (PIMAGE_SECTION_HEADER)(
        (UINT64)(pSectionHeader[i]) + IMAGE_SIZEOF_SECTION_HEADER);
  }

  for (int i = 0; i < pFileHeader->NumberOfSections; i++) {
    /*std::string sec_name;
    for (auto item : pSectionHeader[i]->Name) {
                    sec_name.push_back(item);
    }*/
    if (!strcmp((char *)(pSectionHeader[i]->Name), ".smcsec")) {
      long NumberOfSMCEnctrys =
          pSectionHeader[i]->SizeOfRawData / sizeof(SMCSEC_ENTRY64_T);
      SMCSEC_ENTRY64_T *psmcsec_entry =
          (SMCSEC_ENTRY64_T *)((UINT64)BaseAddr +
                               (UINT64)RVAToFOA64(
                                   pSectionHeader[i]->VirtualAddress));
      for (int j = 1; j <= NumberOfSMCEnctrys; j++) {
        SMCSEC_ENTRY64_T smc;
        if (psmcsec_entry->func_start == 0x0) {
          psmcsec_entry =
              (SMCSEC_ENTRY64_T *)((UINT64)psmcsec_entry + sizeof(UINT64));
            continue;
        }
          
        smc.func_start = psmcsec_entry->func_start - GetImageBase();
        
        // std::cout << std::hex << psmcsec_entry->func_end << std::endl;
        if (strstr(GetSecNameOf64(smc.func_start).c_str(), ".rdata")) {
          int length = psmcsec_entry->func_end;
          UINT64 symbolStart = psmcsec_entry->func_start;

          smc.func_end = smc.func_start + length;
        } else {
          smc.func_end = psmcsec_entry->func_end - GetImageBase();
        }

        if (psmcsec_entry->reloc_start == 0x0) {
          Modify_8Bytes((UINT64)psmcsec_entry, 0xFFFFFFFFFFFFFFFF);
          return encrypt_funcs;
        } else if (psmcsec_entry->reloc_start != 0x123456789abcdef) {
          encrypt_funcs.clear();
          return encrypt_funcs;
        }
        smc.reloc_start = (UINT64)psmcsec_entry + 2 * sizeof(UINT64);

        // std::cout << std::hex << psmcsec_entry->reloc_end << std::endl;
        smc.reloc_end = (UINT64)psmcsec_entry + 3 * sizeof(UINT64);
        encrypt_funcs.push_back(smc);
        // psmcsec_entry = (SMCSEC_ENTRY64_T*)((UINT64)psmcsec_entry +
        // sizeof(SMCSEC_ENTRY64_T));
        psmcsec_entry =
            (SMCSEC_ENTRY64_T *)((UINT64)psmcsec_entry + 4 * sizeof(UINT64));
      }
    }
  }

  return encrypt_funcs;
}

std::vector<SMCSEC_ENTRY32_T> PEParser::GetEncryptFuncs32() {
  PIMAGE_OPTIONAL_HEADER32 pOptionalHeader = GetOptionalHeader32();
  PIMAGE_FILE_HEADER pFileHeader = GetFileHeader32();
  PIMAGE_SECTION_HEADER pSectionHeader[10];
  pSectionHeader[0] = (PIMAGE_SECTION_HEADER)((UINT64)(pOptionalHeader) +
                                              sizeof(IMAGE_OPTIONAL_HEADER32));

  std::vector<SMCSEC_ENTRY32_T> encrypt_funcs;
  for (int i = 0; i < pFileHeader->NumberOfSections - 1; i++) {
    pSectionHeader[i + 1] = (PIMAGE_SECTION_HEADER)(
        (UINT64)(pSectionHeader[i]) + IMAGE_SIZEOF_SECTION_HEADER);
  }

  for (int i = 0; i < pFileHeader->NumberOfSections; i++) {
    /*std::string sec_name;
    for (auto item : pSectionHeader[i]->Name) {
                    sec_name.push_back(item);
    }*/
    if (!strcmp((char *)(pSectionHeader[i]->Name), ".smcsec")) {
      long NumberOfSMCEnctrys =
          pSectionHeader[i]->SizeOfRawData / sizeof(SMCSEC_ENTRY32_T);
      SMCSEC_ENTRY32_T *psmcsec_entry =
          (SMCSEC_ENTRY32_T *)((UINT64)BaseAddr +
                               (UINT64)RVAToFOA32(
                                   pSectionHeader[i]->VirtualAddress));
      for (int j = 1; j <= NumberOfSMCEnctrys; j++) {
        SMCSEC_ENTRY32_T smc;
        if (psmcsec_entry->func_start == 0x0) {
          psmcsec_entry = (SMCSEC_ENTRY32_T *)((UINT64)psmcsec_entry +
                                               sizeof(UINT32));
          continue;
        }
        // std::cout << std::hex << psmcsec_entry->func_start << std::endl;
        smc.func_start = psmcsec_entry->func_start - GetImageBase();
        if (strstr(GetSecNameOf32(smc.func_start).c_str(), ".rdata")) {
          int length = psmcsec_entry->func_end;
          UINT32 symbolStart = psmcsec_entry->func_start;
          smc.func_end = smc.func_start + length;
        } else {
          smc.func_end = psmcsec_entry->func_end - GetImageBase();
        
        }

        // std::cout << std::hex << psmcsec_entry->func_end << std::endl;
        //smc.func_end = psmcsec_entry->func_end - GetImageBase();
        // std::cout << std::hex << psmcsec_entry->reloc_start << std::endl;
        if (psmcsec_entry->reloc_start == 0x0) {    // end of smcsec
          Modify_4Bytes((UINT64)psmcsec_entry, 0xFFFFFFFF);
          break;
        } else if (psmcsec_entry->reloc_start != 0x12345678) {    // has been encrypted
          encrypt_funcs.clear();
          return encrypt_funcs;
        }   
        smc.reloc_start = (UINT64)psmcsec_entry + 2 * sizeof(UINT32);
        // std::cout << std::hex << psmcsec_entry->reloc_end << std::endl;
        smc.reloc_end = (UINT64)psmcsec_entry + 3 * sizeof(UINT32);
        encrypt_funcs.push_back(smc);
        psmcsec_entry = (SMCSEC_ENTRY32_T *)((UINT64)psmcsec_entry +
                                             sizeof(SMCSEC_ENTRY32_T));
      }
    }
  }

  return encrypt_funcs;
}

std::vector<std::pair<int, int>> PEParser::GetEncryptFunctionInfo() {
  std::vector<std::pair<int, int>>
      encrypt_funcs_info; // Contain the start FOA and size of all encrtpt
                          // functions
  if (ISA == X86) {
    std::vector<SMCSEC_ENTRY32_T> encrypt_funcs = GetEncryptFuncs32();
    for (auto item : encrypt_funcs) {
      int start_foa = RVAToFOA32(item.func_start);
      int size = item.func_end - item.func_start;
      encrypt_funcs_info.push_back(std::make_pair(start_foa, size));
    }
  } else if (ISA == X64) {
    std::vector<SMCSEC_ENTRY64_T> encrypt_funcs = GetEncryptFuncs64();
    for (auto item : encrypt_funcs) {
      int start_foa = RVAToFOA64(item.func_start);
      int size = item.func_end - item.func_start;
      encrypt_funcs_info.push_back(std::make_pair(start_foa, size));
    }
  }

  return encrypt_funcs_info;
}

std::vector<std::set<int>> PEParser::GetRelocationInfo() {
  std::vector<std::set<int>> RelocItems;
  if (ISA == X86) {
    std::vector<SMCSEC_ENTRY32_T> encrypt_funcs = GetEncryptFuncs32();
    std::vector<RELOC_ITEM_T<uint32_t>> relocs = ParseRelocationTable32();
    std::vector<uint32_t> reloc_addrs;
    for (auto item : relocs) {
      if ((strstr(item.section.c_str(), ".text") ||
           strstr(item.section.c_str(), ".rdata")) &&
          (!strstr(item.type.c_str(), "ABSOLUTE"))) {
        reloc_addrs.push_back(item.RVA);
      }
    }
    int func_index = 0;
    while (func_index < encrypt_funcs.size()) {
      int i = 0;
      std::set<int> RelocItemsInThisFunc;
      for (; i < reloc_addrs.size(); i++) {
        if (reloc_addrs[i] >= encrypt_funcs[func_index].func_start &&
            reloc_addrs[i] <= encrypt_funcs[func_index].func_end &&
            (i == 0 || reloc_addrs[i - 1] < encrypt_funcs[func_index] .func_start)) { // Found the first reloction item in the
                                     // code region of encrypt_funcs[func_index]
          UINT64 addr = ((UINT64)BaseAddr & 0xFFFFFFFF00000000) +
                        (UINT64)encrypt_funcs[func_index]
                            .reloc_start; // 32bit addr to 64bit addr
          Modify_4Bytes(addr, (uint32_t)i);
          encrypt_funcs[func_index].reloc_start = i;
          // relocs.insert(RVAToFOA32(reloc_addrs[i]) -
          // RVAToFOA32(encrypt_funcs[func_index].func_start));
        }
        if (reloc_addrs[i] >= encrypt_funcs[func_index].func_start &&
            reloc_addrs[i] <= encrypt_funcs[func_index].func_end &&
            (i == reloc_addrs.size() - 1 || reloc_addrs[i + 1] > encrypt_funcs[func_index].func_end)) { // Found the last relocation item in the code
                                   // region of encrypt_funcs[func_index]
          UINT64 addr = ((UINT64)BaseAddr & 0xFFFFFFFF00000000) +
                        (UINT64)encrypt_funcs[func_index].reloc_end;
          Modify_4Bytes(addr, (UINT32)i);
          encrypt_funcs[func_index].reloc_end = i;
          for (int j = encrypt_funcs[func_index].reloc_start;
               j <= encrypt_funcs[func_index].reloc_end; j++) {
            RelocItemsInThisFunc.insert(
                RVAToFOA32(reloc_addrs[j]) -
                RVAToFOA32(encrypt_funcs[func_index].func_start));
          }
          RelocItems.push_back(RelocItemsInThisFunc);
          func_index++;
          break;
        }
      }

      if (i == reloc_addrs.size()) {
        RelocItems.push_back(RelocItemsInThisFunc);
        UINT64 addr = ((UINT64)BaseAddr & 0xFFFFFFFF00000000) +
                      (UINT64)encrypt_funcs[func_index]
                          .reloc_start; // 32bit addr to 64bit addr
        Modify_4Bytes(addr, (uint32_t)-1);
        addr = ((UINT64)BaseAddr & 0xFFFFFFFF00000000) +
               (UINT64)encrypt_funcs[func_index]
                   .reloc_end; // 32bit addr to 64bit addr
        Modify_4Bytes(addr, (uint32_t)-1);
        func_index++;
      }
    }
  } else if (ISA == X64) {
    std::vector<SMCSEC_ENTRY64_T> encrypt_funcs = GetEncryptFuncs64();
    std::vector<RELOC_ITEM_T<uint64_t>> relocs = ParseRelocationTable64();
    std::vector<uint64_t> reloc_addrs;
    for (auto item : relocs) {
      if ((strstr(item.section.c_str(), ".text") ||
           strstr(item.section.c_str(), ".rdata")) &&
          (!strstr(item.type.c_str(), "ABSOLUTE"))) {
        reloc_addrs.push_back(item.RVA);
      }
    }
    int func_index = 0;
    while (func_index < encrypt_funcs.size()) {
      int i = 0;
      std::set<int> relocs;
      for (; i < reloc_addrs.size(); i++) {
        if (reloc_addrs[i] >= encrypt_funcs[func_index].func_start &&
            reloc_addrs[i] <= encrypt_funcs[func_index].func_end &&
            (i == 0 ||
             reloc_addrs[i - 1] <
                 encrypt_funcs[func_index]
                     .func_start)) { // Found the first reloction item in the
                                     // code region of encrypt_funcs[func_index]
          // UINT64 addr = ((UINT64)ImageBase & 0xFFFFFFFF00000000) +
          // (UINT64)encrypt_funcs[func_index].reloc_start;   //32bit addr to
          // 64bit addr
          Modify_8Bytes(encrypt_funcs[func_index].reloc_start, (uint64_t)i);
          encrypt_funcs[func_index].reloc_start = i;
          // relocs.insert(RVAToFOA32(reloc_addrs[i]) -
          // RVAToFOA32(encrypt_funcs[func_index].func_start));
        }
        if (reloc_addrs[i] >= encrypt_funcs[func_index].func_start &&
            reloc_addrs[i] <= encrypt_funcs[func_index].func_end &&
            (i == reloc_addrs.size() - 1 ||
             reloc_addrs[i + 1] >
                 encrypt_funcs[func_index]
                     .func_end)) { // Found the last relocation item in the code
                                   // region of encrypt_funcs[func_index]
          // UINT64 addr = ((UINT64)ImageBase & 0xFFFFFFFF00000000) +
          // (UINT64)encrypt_funcs[func_index].reloc_end;
          Modify_8Bytes(encrypt_funcs[func_index].reloc_end, (UINT64)i);
          encrypt_funcs[func_index].reloc_end = i;
          for (int j = encrypt_funcs[func_index].reloc_start;
               j <= encrypt_funcs[func_index].reloc_end; j++) {
            relocs.insert(RVAToFOA64(reloc_addrs[j]) -
                          RVAToFOA64(encrypt_funcs[func_index].func_start));
          }
          RelocItems.push_back(relocs);
          func_index++;
          break;
        }
      }

      if (i == reloc_addrs.size()) {
        RelocItems.push_back(relocs);
        Modify_8Bytes(encrypt_funcs[func_index].reloc_start, (uint64_t)-1);
        Modify_8Bytes(encrypt_funcs[func_index].reloc_end, (UINT64)-1);
        func_index++;
      }
    }
  }

  return RelocItems;
}

#endif