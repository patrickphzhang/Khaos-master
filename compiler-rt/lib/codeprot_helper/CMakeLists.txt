add_compiler_rt_component(codeprot_helper)

set(ANTIVM_SOURCES
	antivm_helper.cpp)
set(ANTIDUMP_SOURCES
	antidump_helper.cpp)
set(SEH_SOURCES
	seh_helper.cpp)
set(DEOBFUSCATE_SOURCES
	deobfuscate_helper.cpp)
set(SMC_SOURCES
	smc_helper.cpp)
set(PGV_SOURCES
	pageguard_helper.cpp)
set(FUSION_SOURCES
	fusion_helper.cpp)


include_directories(..)

foreach(arch ${CFI_SUPPORTED_ARCH})

	add_sanitizer_rt_symbols(clang_rt.codeprot.antivm
		ARCHS ${arch}
		PARENT_TARGET codeprot_helper
		EXTRA codeprot.syms.extra)

	add_sanitizer_rt_symbols(clang_rt.codeprot.antidump
		ARCHS ${arch}
		PARENT_TARGET codeprot_helper
		EXTRA codeprot.syms.extra)

	add_sanitizer_rt_symbols(clang_rt.codeprot.seh
		ARCHS ${arch}
		PARENT_TARGET codeprot_helper
		EXTRA codeprot.syms.extra)

	add_sanitizer_rt_symbols(clang_rt.codeprot.deobfuscate
		ARCHS ${arch}
		PARENT_TARGET codeprot_helper
		EXTRA codeprot.syms.extra)
	
	add_sanitizer_rt_symbols(clang_rt.codeprot.smc
		ARCHS ${arch}
		PARENT_TARGET codeprot_helper
		EXTRA codeprot.syms.extra)

	add_sanitizer_rt_symbols(clang_rt.codeprot.pageguard
		ARCHS ${arch}
		PARENT_TARGET codeprot_helper
		EXTRA codeprot.syms.extra)

	add_sanitizer_rt_symbols(clang_rt.codeprot.fusion
		ARCHS ${arch}
		PARENT_TARGET codeprot_helper
		EXTRA codeprot.syms.extra)


	add_compiler_rt_runtime(clang_rt.codeprot.antivm
		STATIC
		ARCHS ${arch}
		SOURCES ${ANTIVM_SOURCES}
		PARENT_TARGET codeprot_helper)

	add_compiler_rt_runtime(clang_rt.codeprot.antidump
		STATIC
		ARCHS ${arch}
		SOURCES ${ANTIDUMP_SOURCES}
		PARENT_TARGET codeprot_helper)

	add_compiler_rt_runtime(clang_rt.codeprot.seh
		STATIC
		ARCHS ${arch}
		SOURCES ${SEH_SOURCES}
		PARENT_TARGET codeprot_helper)

	add_compiler_rt_runtime(clang_rt.codeprot.deobfuscate
		STATIC
		ARCHS ${arch}
		SOURCES ${DEOBFUSCATE_SOURCES}
		PARENT_TARGET codeprot_helper)

	add_compiler_rt_runtime(clang_rt.codeprot.smc
		STATIC
		ARCHS ${arch}
		SOURCES ${SMC_SOURCES}
		PARENT_TARGET codeprot_helper)

	add_compiler_rt_runtime(clang_rt.codeprot.pageguard
		STATIC
		ARCHS ${arch}
		SOURCES ${PGV_SOURCES}
		PARENT_TARGET codeprot_helper)

	add_compiler_rt_runtime(clang_rt.codeprot.fusion
		STATIC
		ARCHS ${arch}
		SOURCES ${FUSION_SOURCES}
		PARENT_TARGET codeprot_helper)

endforeach()




