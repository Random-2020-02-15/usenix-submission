# If we don't need RTTI or EH, there's no reason to export anything
# from the SRPass plugin.
if( NOT LLVM_REQUIRES_RTTI )
  if( NOT LLVM_REQUIRES_EH )
    set(LLVM_EXPORTED_SYMBOL_FILE ${CMAKE_CURRENT_SOURCE_DIR}/SRPass.exports)
  endif()
endif()

if(WIN32 OR CYGWIN)
  set(LLVM_LINK_COMPONENTS Core Support)
endif()

add_llvm_library( SRPass MODULE BUILDTREE_ONLY
  SCIPass.cpp
  DynamicCallCounter.cpp
  DynPass.cpp
  DynPass2.cpp
  StaPass.cpp
  SafePass.cpp
  SCClean.cpp
  utils.cpp
  CostModel.cpp

  PLUGIN_TOOL
  opt
  )

add_dependencies(SRPass LLVMInstrumentation)

# Create symlinks for SR-clang.rb
add_custom_command(OUTPUT ${CMAKE_BINARY_DIR}/bin/SR-clang
  COMMAND cd ${CMAKE_BINARY_DIR}/bin && ln -s ${CMAKE_CURRENT_SOURCE_DIR}/SR-clang.rb SR-clang
  COMMENT Creating symlink for SR-clang
  VERBATIM)
add_custom_command(OUTPUT ${CMAKE_BINARY_DIR}/bin/SR-clang++
  COMMAND cd ${CMAKE_BINARY_DIR}/bin && ln -s ${CMAKE_CURRENT_SOURCE_DIR}/SR-clang.rb SR-clang++
  COMMENT Creating symlink for SR-clang++
  VERBATIM)
add_custom_command(OUTPUT ${CMAKE_BINARY_DIR}/bin/SR-ranlib
  COMMAND cd ${CMAKE_BINARY_DIR}/bin && ln -s ${CMAKE_CURRENT_SOURCE_DIR}/SR-clang.rb SR-ranlib
  COMMENT Creating symlink for SR-ranlib
  VERBATIM)
add_custom_command(OUTPUT ${CMAKE_BINARY_DIR}/bin/SR-ar
  COMMAND cd ${CMAKE_BINARY_DIR}/bin && ln -s ${CMAKE_CURRENT_SOURCE_DIR}/SR-clang.rb SR-ar
  COMMENT Creating symlink for SR-ar
  VERBATIM)
add_custom_target(SR_clang_symlinks
  ALL
  DEPENDS ${CMAKE_BINARY_DIR}/bin/SR-clang
          ${CMAKE_BINARY_DIR}/bin/SR-clang++
          ${CMAKE_BINARY_DIR}/bin/SR-ranlib
          ${CMAKE_BINARY_DIR}/bin/SR-ar)