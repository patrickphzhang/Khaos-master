#include "FileParser.h"
#include "Cypher.h"
#ifdef _WIN32
#include "PEParser.h"
#endif
#ifdef __linux__
#include "ELFParser.h"
#endif
int count = 0;

void PrintHelp(){
    
}


int EncryptFunction(FileParser* parser, std::pair<int, int> func, std::set<int> relocs) {
    return 1;
}

int main(int argc, char* argv[]){
    

    return 0;
}