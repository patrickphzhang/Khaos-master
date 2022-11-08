#include "FileParser.h"


// File Read/Write APIs
void FileParser::Modify_Byte(intptr_t addr, uint8_t byte) {
	*(uint8_t*)addr = byte;
}
void FileParser::Modify_2Bytes(intptr_t addr, uint16_t byte) {
	*(uint16_t*)addr = byte;
}
void FileParser::Modify_4Bytes(intptr_t addr, uint32_t byte) {
	*(uint32_t*)addr = byte;
}
void FileParser::Modify_8Bytes(intptr_t addr, uint64_t byte) {
	*(uint64_t*)addr = byte;
}
uint8_t FileParser::Read_Byte(intptr_t addr) {
	const uint8_t byte = *(uint8_t*)(addr);
	return byte;
}
uint16_t FileParser::Read_2Bytes(intptr_t addr) {
	const uint16_t byte = *(uint16_t*)(addr);
	return byte;
}
uint32_t FileParser::Read_4Bytes(intptr_t addr) {
	const uint32_t byte = *(uint32_t*)(addr);
	return byte;
}
uint64_t FileParser::Read_8Bytes(intptr_t addr) {
	const uint64_t byte = *(uint64_t*)(addr);
	return byte;
}

// Simple implementation of Key Genaration 
uint64_t FileParser::GenerateEncryptionKey() {
	return 0x123456789abcdef;
}


