#pragma once
#pragma once
#include <cstdlib>
#include <stdint.h>
#include <string>
#include <iostream>
#include <set>
enum cypher_mode {
    AES_128,
    AES_256,
    XOR
};
class Cypher {
public:

    Cypher(uint64_t key) { xor_key.key_i = key; cypher_mode = XOR; };
    std::string encrypt(std::string plaintext, std::set<int> func_relocs, int ISA);
private:

    union xor_key
    {
        uint64_t key_i;
        unsigned char key_c[sizeof(uint64_t)];
    }xor_key;
    int cypher_mode;
    //std::string encrypt_AES128(std::string plaintext);
    std::string encrypt_XOR(std::string plaintext, std::set<int> func_relocs, int ISA);

};