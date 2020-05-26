project(llvmtest)
cmake_minimum_required(VERSION 2.8)

find_package(LLVM REQUIRED CONFIG)

message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")
message(STATUS "Using LLVMConfig.cmake in: ${LLVM_DIR}")

# Needed to use support library

set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fno-rtti -std=c++14")


include_directories(${LLVM_INCLUDE_DIRS})
add_definitions(${LLVM_DEFINITIONS})


add_executable(llvmtest 
#DT_LI.cpp
#test_domTree.cpp //has some error
#main.cpp
#transFILE.cpp
#loop.cpp
#Toposort.cpp
#mulMap.cpp
test.cpp
newInterpreter.cpp
)

llvm_map_components_to_libnames(llvm_libs BitWriter Core IPO IrReader InstCombine Instrumentation Target Linker Analysis ScalarOpts Support interpreter native)


target_link_libraries(llvmtest
    pthread
    dl
)

#link llvm component
target_link_libraries(llvmtest ${llvm_libs})


#link llvm library
target_link_libraries(llvmtest
${llvm_libs}
mathsat
gmp
)
