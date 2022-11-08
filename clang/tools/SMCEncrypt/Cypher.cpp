#include "Cypher.h"
std::string Cypher::encrypt(std::string plaintext, std::set<int> func_relocs, int ISA) {
    std::string res = "";
    switch (cypher_mode)
    {
    case AES_128:
        //res = encrypt_AES128(plaintext);
        break;
    case XOR:
        res = encrypt_XOR(plaintext, func_relocs, ISA);
        break;

    default:
        std::cout << "[ERROR] Unknown Encrypt Mode!\n";
        break;
    }
    return res;
}

std::string Cypher::encrypt_XOR(std::string plaintext, std::set<int> func_relocs, int ISA) {
    int length = plaintext.size();
    std::string cyphertext;
    for (int i = 0; i < length; i++) {
        if (func_relocs.find(i) != func_relocs.end()) {   // If we found a relocation item in this func, skip the continuous 4/8 Bytes
            if (ISA == 2) {
                for (int j = i; j < i + 8; j++) {
                    cyphertext.push_back(plaintext[j]);
                }
                i += 7;

            }
            else if (ISA == 1) {
                for (int j = i; j < i + 4; j++) {
                    cyphertext.push_back(plaintext[j]);
                }
                i += 3;
            }
            continue;
        }
        cyphertext.push_back(plaintext[i] ^ xor_key.key_c[i % sizeof(uint64_t)]);
    }
    return cyphertext;

}

//std::string Cypher::encrypt_AES128(std::string plaintext) {
//    return "";
//}