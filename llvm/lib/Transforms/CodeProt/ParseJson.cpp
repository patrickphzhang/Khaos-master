//===- ParseJson.cpp ------------------------------------- ---------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// 
// 
//
//===----------------------------------------------------------------------===//

#include "llvm/Transforms/CodeProt/Utils.h"

#define DEBUG_TYPE "parsejson"

static cl::opt<std::string> JsonFile("file", cl::value_desc("filename"),
        cl::desc("A file containing list of functions to protect"), cl::Hidden);
cl::opt<int> RatioGlobal("ratio", cl::init(0), cl::Hidden,
		cl::desc("Protect ratio for all types"));
cl::opt<int> RatioInterFunctionFusion("ratio-interfusion", cl::init(0), cl::Hidden,
		cl::desc("Protect ratio for InterFunctionFusion"));
cl::opt<int> RatioObfuscation("ratio-obfuscation", cl::init(0), cl::Hidden,
		cl::desc("Protect ratio for obfuscation"));
cl::opt<int> RatioInterShuffle("ratio-intershuffle", cl::init(0), cl::Hidden,
		cl::desc("Protect ratio for intershuffle"));
cl::opt<int> LevelDeepFusion("level-deepfusion", cl::init(0), cl::Hidden,
		cl::desc("Deep fusion level"));
//cl::opt<unsigned long long> PayloadKey("payload-key", cl::init(0),
//        cl::Hidden, cl::desc("Obfuscation key for payload section"));
cl::opt<bool> EnableCodeObf("enable-codeobf", cl::init(false), cl::Hidden,
		cl::desc("Enable Code Obfuscation"));
cl::opt<bool> EnableCodeObfSub("enable-codeobf-sub", cl::init(false), cl::Hidden,
		cl::desc("Enable Code Obfuscation Substitution"));
cl::opt<bool> EnableCodeObfFla("enable-codeobf-fla", cl::init(false), cl::Hidden,
		cl::desc("Enable Code Obfuscation Flattening"));
cl::opt<bool> EnableCodeObfBog("enable-codeobf-bog", cl::init(false), cl::Hidden,
		cl::desc("Enable Code Obfuscation Bogus"));
cl::opt<bool> EnableInterFunctionFusion("enable-interfusion", cl::init(false), cl::Hidden,
		cl::desc("Enable InterFunctionFusion"));
cl::opt<bool> FissionedFunctionOnly("fissioned-function-only", cl::init(false), cl::Hidden,
		cl::desc("Only Fusion Fissioned Functions"));
cl::opt<bool> OriginFunctionOnly("origin-function-only", cl::init(false), cl::Hidden,
		cl::desc("Only Fusion Origin Functions"));
cl::opt<bool> EnableInterFunctionShufflePass("enable-intershuffle",
				cl::desc("Enable InterFunctionShuffle Pass"),
				cl::init(false), cl::Hidden);
cl::opt<bool> EnableInterFunctionShuffleOptPass("enable-intershuffle-opt",
				cl::desc("Enable InterFunctionShuffleOpt Pass"),
				cl::init(false), cl::Hidden);
cl::opt<bool> EnableTransformStat("enable-transform-stat", 
                cl::desc("Pass can write their tansform-statistics into a json file"),
                cl::init(false),
                cl::Hidden);

namespace llvm {
    bool HasJsonParsed = false;
    Json::Value JsonObj;
}

namespace {
    struct ParseJsonPass : public ModulePass {
        static char ID; // Pass identification, replacement for typeid
        ParseJsonPass() : ModulePass(ID) {}

        bool runOnModule(Module &M) override;

    };

}

char ParseJsonPass::ID = 0;

bool ParseJsonPass::runOnModule(Module &M) {

    // LLVMContext &C = M.getContext();
	// Type *VoidTy = Type::getVoidTy(C);
    // FunctionType *PrintFunctionType = FunctionType::get(VoidTy, {IntegerType::getInt8PtrTy(C)}, false);
	// Function *PrintFunction = cast<Function>(M.getOrInsertFunction("print", PrintFunctionType).getCallee());

	// for (auto &F : M) {
    //     if (F.isIntrinsic() || F.isDeclaration() || F.size() == 0)
    //         continue;
    //     BasicBlock &entryBB = F.getEntryBlock();
    //     Instruction &firstInst = entryBB.front();
	// 	//IRBuilder<> IRB(&firstInst);
    //     for (auto &BB : F)
    //     {
    //         if (BB.hasName() && BB.size() > 0)
    //         {
    //             BasicBlock::iterator IP = BB.getFirstInsertionPt();
    //             IRBuilder<> IRB(&(*IP));
    //             std::string ID("");
    //             //ID.append(itostr(BB.getValueID))
    //             IRB.CreateCall(PrintFunction, {IRB.CreateGlobalStringPtr(BB.getName())});
    //         }
    //     }
    //     if (entryBB.size() > 0)
    //     {
    //         BasicBlock::iterator IP = BB.getFirstInsertionPt();
    //         IRBuilder<> IRB(&(*IP));
    //         IRB.CreateCall(PrintFunction, {IRB.CreateGlobalStringPtr(F.getName())});
    //     }
	// }


        if (HasJsonParsed == false) {
            HasJsonParsed = true;
            srand((int)time(0));

            if (!JsonFile.empty() && RatioGlobal) {
                errs() << "Do not use \"-ratio\" and \"-file\" together!\n";
                exit(1);
            }
            if (!JsonFile.empty()) {
                LLVM_DEBUG(outs() << "[*] Beginning parsing json file.\n");
                Json::Reader reader;
                ifstream fd;
                fd.open(JsonFile);
                if (!reader.parse(fd, JsonObj)) {
                    LLVM_DEBUG(outs() << "\t[*] Opening json failed.\n");
                    fd.close();
                } else {
                    LLVM_DEBUG(outs() << "\t[*] Opening json success.\n");
                }
                LLVM_DEBUG(outs() << "[*] Finishing parsing json file.\n");
            }
        }
    
    // StringRef nof = "getvar_i___next_input_file___clrvar___hash_init___getvar_s___evaluate___handle_special___evaluate___nvalloc___BN_mod_sqrt___EC_GROUP_new_from_ecparameters___sm2_plaintext_size___check_chain_extensions___init_sig_algs___X509_issuer_and_serial_hash___evp_EncryptDecryptUpdate___GENERAL_NAME_dup___tls1_check_sig_alg___cms_RecipientInfo_ktri_decrypt___EC_GROUP_set_generator___chacha_init_key___dsa_sign_setup___ec_scalar_mul_ladder___ftp_statemachine___imap_state_starttls_resp___pop3_state_starttls_resp___smtp_state_starttls_resp___ftp_statemachine___imap_state_capability_resp___pop3_state_capa_resp___sectransp_connect_step1___suboption___create_conn___gtls_connect_step3___nss_do_connect___servercert___suboption___Curl_follow___init_wc_data___config_init___Curl_init_userdefined___conn_is_conn___curl_easy_duphandle___curl_multi_add_handle___Curl_open___curl_multi_remove_handle___close_connect_only___tool_header_cb___tftp_connect___tftp_connect___voutf___Curl_auth_create_plain_message___Curl_ntlm_core_mk_nt_hash___Curl_http_readwrite_headers___readwrite_data___ldap_recv___ftp_state_list___ftp_done___ftp_parse_url_path___Curl_http_output_auth___setcharset___imap_state_fetch_resp___ftp_statemach_act___tftp_send_first___ourWriteOut___dprintf_formatf___verify_certificate___verify_certificate___get_line___ConnectionExists___base64_encode___alloc_addbyter___read_data___parsedate___unescape_word___curl_easy_unescape___Curl_cookie_getlist___parseurlandfillconn___curl_version___curl_easy_unescape___SelectClientCert___Curl_clone_ssl_config___Curl_ssl_config_matches___close_all_connections___Curl_sspi_global_init___mbed_connect_step1___polarssl_connect_step1___tool_header_cb___parse_filename___ConnectionExists___Curl_init_userdefined___sanitize_cookie_path___Curl_http_done___ConnectionExists___darwinssl_connect_step1___parseurlandfillconn___FormAdd___Curl_cookie_add___Curl_cookie_add___schannel_connect_step1___darwinssl_connect_step1___hostmatch___ConnectionExists";
    // StringRef nof(noinlinefunctions);
    // for (auto &F : M) {
    //     if (F.isIntrinsic() || F.isDeclaration() || F.size() == 0)
    //         continue;
    //     if (nof.find(F.getName()) > 0) {
    //         F.addFnAttr(Attribute::NoInline);
    //     }
    // }
	return true;

}


static RegisterPass<ParseJsonPass> X("parsejson", "ParseJson Pass");

ModulePass *llvm::createParseJsonPass() {
    return new ParseJsonPass();
}

