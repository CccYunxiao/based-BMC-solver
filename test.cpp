
#include <llvm/IR/LLVMContext.h>
#include "newInterpreter.h"


int main(int argc, char** argv)  
{  
    if (argc < 2) {  
        errs() << "Expected an argument - IR file name\n";  
        exit(1);  
    }  
    auto& context = getGlobalContext();
    newInterpreter *interpreter = new newInterpreter(argv[1],context);
    

    return 1;
    
}
