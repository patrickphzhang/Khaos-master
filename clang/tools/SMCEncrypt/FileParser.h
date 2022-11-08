#pragma once
#include <string>
#include <iostream>
#include <vector>
#include <cstdlib>
#include <cstdio>
#include <vector>
#include <set>

//#ifdef __linux__
//#include"ELFParser.h"
//#endif


enum ISA {
	UNKNOWN,
	X86,
	X64,
	IA64
};
class FileParser {
public:
	FileParser() = default;
	void Modify_Byte(intptr_t addr, uint8_t byte);
	void Modify_2Bytes(intptr_t addr, uint16_t bytes);
	void Modify_4Bytes(intptr_t addr, uint32_t bytes);
	void Modify_8Bytes(intptr_t addr, uint64_t bytes);

	uint8_t Read_Byte(intptr_t addr);
	uint16_t Read_2Bytes(intptr_t addr);
	uint32_t Read_4Bytes(intptr_t addr);
	uint64_t Read_8Bytes(intptr_t addr);

	uint64_t GenerateEncryptionKey();

	intptr_t GetBaseAddr() {
		return BaseAddr;
	}
	int GetISA() {
		return ISA;
	}


	virtual void OpenFileByName() = 0;
	virtual intptr_t GetImageBase() = 0;
	virtual std::vector<std::pair<int, int>> GetEncryptFunctionInfo() = 0;      // Get start FOA and Size of all funcs to be encrypted
	virtual std::vector<std::set<int>> GetRelocationInfo() = 0;                 // Returns the addresses of all relocation items corresponding to each function
protected:
	std::string FilePath;
	intptr_t ImageBase = 0xffffffff;                  // ImageBase Write in the PE/ELF File
	intptr_t BaseAddr;                   // Pointer to the first byte of the file when the file is mapped in the memory
	int ISA;

};