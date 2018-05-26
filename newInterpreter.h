
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/InstrTypes.h>
#include <llvm/Support/raw_ostream.h>
#include <llvm/ADT/DenseMap.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/CallSite.h>
#include <llvm/IRReader/IRReader.h>
#include <llvm/Support/SourceMgr.h>
#include <llvm/IR/Dominators.h>
#include <llvm/Analysis/LoopInfo.h>
#include <llvm/ADT/SmallVector.h>
#include <sstream>
#include <string>
#include <stdio.h>
#include <mathsat.h>
#include <assert.h>
#include <vector>
#include <boost/iterator/iterator_concepts.hpp>
#include <llvm/Support/TargetSelect.h>
#include <llvm/IR/LegacyPassManager.h>
#include <llvm/Transforms/Scalar.h>

#include <llvm/IR/IRBuilder.h>

using namespace llvm;
using namespace std;

class newInterpreter
{
    char* file_name;
    SMDiagnostic Err;

  
    std::unique_ptr<llvm::Module> module;  
    Module *Mod;
    Function* func;
    BasicBlock* latch;
    
    int max_unroll_time = 20;
    int unroll_time = 1;
    bool has_loop = true;
    bool skipSMT_continue_unroll = false;
    string latch_cond_formula;
    string Transition_latch_exit;
    string end_formula;
    
    msat_config cfg;
    msat_env env;
    msat_term formula;
    msat_result status;
    int res;
    
//     vector<string> latch_cond;
//     vector<string> assert_cond;


public:
    newInterpreter(char* argv,LLVMContext &context)
    {
	file_name=argv;
	check_sat(context);
    }
    ~newInterpreter()
    {
    }
private:
    void getIRModule(LLVMContext &context);
    
    void check_sat(LLVMContext &context);
    
    msat_result encodeIR();
    
    bool LoopUnroll(LLVMContext &context);
    
    void init_MathSAT();
    
    void end_MathSAT();
    
    static void print_model(msat_env env)
    {
	msat_model_iterator iter = msat_create_model_iterator(env);
	assert(!MSAT_ERROR_MODEL_ITERATOR(iter));

	printf("Model:\n");
	while (msat_model_iterator_has_next(iter)) {
	    msat_term t, v;
	    char *s;
	    msat_model_iterator_next(iter, &t, &v);
	    s = msat_term_repr(t);
	    assert(s);
	    printf(" %s = ", s);
	    msat_free(s);
	    s = msat_term_repr(v);
	    assert(s);
	    printf("%s\n", s);
	    msat_free(s);
	}
	msat_destroy_model_iterator(iter);
    }
    
    void declareVarible();
    
    void assertVariable();
    
    ///change llvm::Value to std::string
    string calculateVarible(Value *v );
    
    ///change llvm::Value to std::string
    string calculateVarible(Value *v1 , Value *v2);
    
    ///change llvm::Constant to std::string 
    string calculateConstant(Constant *cv);
    
    ///change Integer to std::string
    string InttoString(unsigned int v);
    
    /*
    void print_assertInfo(msat_env env)
    {
	
	outs()<<"----------------latch relevant variable begin----------------\n";
	while(!latch_cond.empty())
	{
	    const char *lc1 = latch_cond.back().c_str();
	    outs()<<"  "<<lc1<<" = ";
	    msat_term n1 = msat_from_smtlib2(env,lc1);
	    msat_term v1 = msat_get_model_value(env,n1);
	    char* cv = msat_term_repr(v1);
	    outs()<<cv<<"\n";
	    latch_cond.pop_back();
	    msat_free(cv);
	}
	outs()<<"----------------latch relevant variable end----------------\n";
	outs()<<"----------------assert relevant variable begin----------------\n";
	while(!assert_cond.empty())
	{
	    const char *lc1 = assert_cond.back().c_str();
	    outs()<<"  "<<lc1<<" = ";
	    msat_term n1 = msat_from_smtlib2(env,lc1);
	    msat_term v1 = msat_get_model_value(env,n1);
	    char* cv = msat_term_repr(v1);
	    outs()<<cv<<"\n\n";
	    assert_cond.pop_back();
	    msat_free(cv);
	}
	outs()<<"----------------assert relevant variable end----------------\n";
    }
    */
};
