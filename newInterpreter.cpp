
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
#include <map>
#include <boost/iterator/iterator_concepts.hpp>
#include <llvm/Support/TargetSelect.h>
#include <llvm/IR/LegacyPassManager.h>
#include <llvm/Transforms/Scalar.h>
#include <llvm/Transforms/Utils.h>
#include <llvm/IR/IRBuilder.h>
#include "newInterpreter.h"
#include <llvm/IR/Value.h>
using namespace llvm;
using namespace std;


    void newInterpreter::getIRModule(LLVMContext &context)
    {
	module = parseIRFile(file_name, Err, context);
	Mod = module.get();
	if(!Mod)
	{
	    outs()<<"the module is empty...\n";
	}
    }
    
    void newInterpreter::check_sat(LLVMContext &context)
    {
	while ( (unroll_time <= max_unroll_time) && has_loop)
	{
	    getIRModule(context);
// 	    latch_cond.clear();
// 	    assert_cond.clear();
	    skipSMT_continue_unroll = LoopUnroll(context);
	    if(skipSMT_continue_unroll)
	    {
		outs()<<"Time="<<unroll_time<<":UNSAT. continue unroll...\n";
		getchar();
		unroll_time++;
		continue;
	    }
	    
	    status = encodeIR();
	    
	    latch_cond_formula.clear();
	    Transition_latch_exit.clear();
	    end_formula.clear();
	    
	    if((status == MSAT_UNSAT) || (status == MSAT_UNKNOWN))
	    {
		outs()<<"Time="<<unroll_time<<":UNSAT...\n";
		getchar();
		unroll_time++;
		end_MathSAT();
		return;
	    }else
	    {
		print_model(env);
// 		print_assertInfo(env);
		outs()<<"Time="<<unroll_time<<":SAT. You need to check whether to unroll...\n";
		getchar();
		unroll_time++;
		end_MathSAT();
		continue;
	    }
	}
	return;
    }
    
    msat_result newInterpreter::encodeIR()
    {
	init_MathSAT();
	
	declareVarible();
	
	assertVariable();
	
	status = msat_solve(env);
	//func->dump();
	return status;
    }
    
    bool newInterpreter::LoopUnroll(LLVMContext &context)
    {
	//unroll the loop
	llvm::legacy::PassManager lpm;
	lpm.add(createPromoteMemoryToRegisterPass());
	lpm.add(createLoopSimplifyPass());
	lpm.add(createLoopRotatePass());
	lpm.add(createLCSSAPass());
// 	int threshold = UINT_MAX;
// 	int unrollCount = unroll_time;
// 	int allowPartial = 1;
	lpm.add(createLoopUnrollPass(UINT_MAX,unroll_time,1));
	lpm.add(createInstructionNamerPass());
	//lpm.add(createLoopRerollPass());
	//lpm.add(new looptest());
	lpm.run(*Mod);
	
	func = Mod->getFunction("main");
	
	
// 	func->dump();
	assert(func);
	
	//get loop info
	DominatorTree dt;
	dt.recalculate(*func);
	LoopInfo li;
	li.analyze(dt);
	
	if(li.begin()==li.end())
	{
	    has_loop = false;
	}else
	{
	    has_loop = true;
	}
	
	for(LoopInfo::iterator i=li.begin(),e=li.end();i!=e;i++)
	{
	    Loop *L = *i;

	    BasicBlock* header = L->getHeader();
	    
	    latch = L->getLoopLatch();
	    // TerminatorInst* latch_end = latch->getTerminator();
	    // BranchInst* latch_term = dyn_cast<BranchInst>(latch_end);
	    BranchInst* latch_term = dyn_cast<BranchInst>(latch->getTerminator());

	    SmallVector<BasicBlock*,8> bb_Exits;
	    L->getExitBlocks(bb_Exits);
	    if(bb_Exits.empty())
		errs()<<"SmallVector is empty\n";
	    BasicBlock *exit_bb = bb_Exits[0];
	    
	    
	    //dump the names of header,latch and exit BasicBlock
	    outs()<<"\n-------------loop-info-start----------------\n";
	    outs()<<"header:"<<header->getName()<<'\n';
	    outs()<<"latch:"<<latch->getName()<<'\n';
	    outs()<<"exit:"<<exit_bb->getName()<<"\n";
	    for(int n=1;n<bb_Exits.size();n++)
	    {
		outs()<<"exit:"<<bb_Exits[n]->getName()<<"\n";
		if(exit_bb != bb_Exits[n])
		{
		    outs()<<"there are many exit block in the loop...\n";
		    assert(false);
		}
	    }
	    outs()<<"--------------loop-info-end-----------------\n";
	    
	    
	    if(latch_term->getNumSuccessors()==1)
	    {
		//continue unroll loop
		skipSMT_continue_unroll=true;
		return skipSMT_continue_unroll;
	    }
	    
	    
	    for(auto header_i = header->begin();header_i!=header->end();header_i++)
	    {
		
		PHINode* phi = dyn_cast<PHINode>(header_i);
		if(!phi)
		    break;
		
		
		for(unsigned int n=0;n < phi->getNumIncomingValues();n++)
		{

		    if(phi->getIncomingBlock(n) == latch)
		    {
			phi->removeIncomingValue(n);
			n--;
		    }
		    
		}
		
	    }
	    
// 	    latch_cond_formula.clear();
// 	    Transition_latch_exit.clear();
	    if(latch_term->getSuccessor(0)==header )
	    {
		Value* latch_term_cond = latch_term->getCondition();
		const string latchName = "$"+latch->getName().str();
		const string icmpName = "$"+latch_term_cond->getName().str();
		latch_cond_formula = "(and "+latchName+" (=> "+latchName+" "+icmpName+"))";
		Transition_latch_exit = "(assert (= (and "+latchName+" (not "+icmpName+")) "+latchName+"_"+latch_term->getSuccessor(1)->getName().str()+"))";
		end_formula = end_formula +latchName+" ";
// 		latch_cond.push_back(latchName);
// 		latch_cond.push_back(icmpName);
	    }
// 	    else if(latch_term->getSuccessor(1)==header )
// 	    {
// 		Value* latch_term_cond = latch_term->getCondition();
// 		latch_cond_formula = "(and $"+latch->getName().str()+" (not $"+latch_term_cond->getName().str()+"))";
// 		Transition_latch_exit = "(assert (= (and $"+latch->getName().str()+" $"+latch_term_cond->getName().str()+") $"+latch->getName().str()+"_"+latch_term->getSuccessor(0)->getName().str()+"))";
// 	    }
	    
	    latch_term->dropAllReferences();
	    latch_term->removeFromParent();
	    IRBuilder<> builder(context);
	    builder.SetInsertPoint(latch);
	    builder.CreateBr(exit_bb);
	    
	    // func->dump();

	}
	skipSMT_continue_unroll = false;
	return skipSMT_continue_unroll;
    }
    
    void newInterpreter::init_MathSAT()
    {
	cfg = msat_create_config();
	msat_set_option(cfg,"model_generation","true");
	env = msat_create_env(cfg);
	
    }
    
    void newInterpreter::end_MathSAT()
    {
	msat_destroy_env(env);
	msat_destroy_config(cfg);
    }
    
    
    void newInterpreter::declareVarible()
    {
	if(!func)
	    return;

	string decla_formulas;

// 	outs()<<"(set-logic QF_BV)\n";
	for(iplist<BasicBlock>::iterator iter = func->getBasicBlockList().begin();
	    iter != func->getBasicBlockList().end();
            iter++)
	{
	    ///output declare bbi
	    decla_formulas = decla_formulas+ "(declare-fun $"+iter->getName().str()+" () Bool)";
	    outs()<<"(declare-fun $"<<iter->getName().str()<<" () Bool)\n";
	    
// 	    outs()<<iter->getName().str()<<" = "<<iter->getNumUses()<<'\n';
	    
	    ///declare transition
	    int succ_num = iter->getTerminator()->getNumSuccessors();
	    for(int i=0;i<succ_num;i++)
	    {
		decla_formulas = decla_formulas+ "(declare-fun $"+iter->getName().str()+"_"+iter->getTerminator()->getSuccessor(i)->getName().str()+" () Bool)";
		outs()<<"(declare-fun $"<<iter->getName().str()<<"_"<<iter->getTerminator()->getSuccessor(i)->getName().str()<<" () Bool)\n";
	    }

	    ///output declare varible
	    for(auto inst_i = iter->begin(),inst_e = iter->end();
		(inst_i != inst_e) && (!inst_i->isTerminator());
		inst_i++)
	    {

		string s;
		///Integer bitwith are i1 i2 i4 i8 i16 i32 ...
		if(inst_i->getType()->isIntegerTy())
		{
		    unsigned int bitwith = inst_i->getType()->getIntegerBitWidth();
		    if(bitwith > 1)
		    {
			s = "(declare-fun $"+inst_i->getName().str()+" () (_ BitVec "+InttoString(bitwith)+"))";
		    }else
		    {
			s = "(declare-fun $"+inst_i->getName().str()+" () Bool)";
		    }
		    
// 		    if(bitwith==1)
// 		    {
// 			s = "(declare-fun $"+inst_i->getName().str()+" () (_ BitVec 1))";
// 		    }else if(bitwith<=64)
// 		    {
// 		    ///create Int varible , the following note is the SMT-libv2 format
// 		    ///(declare-fun x () (_ BitVec 64))
// 			s = "(declare-fun $"+inst_i->getName().str()+" () (_ BitVec 64) )";
// 		    }else
// 		    {
// 			outs()<<"the BitVector's width is larger than the size of Int...\n";
// 		    }
		    
		}else if(!inst_i->hasName() && (inst_i->getOpcode() == Instruction::Call))
		{
		    continue;
		}else
		{
		    // inst_i->dump();
		    outs()<<";this type of varible had not defined ...\n";
		}
		decla_formulas = decla_formulas+s;
		outs()<<s<<'\n';
	    }
	}
	
	
	const char *k = decla_formulas.c_str();
// 	outs()<<k<<'\n';
	formula = msat_from_smtlib2(env,k);
	assert(!MSAT_ERROR_TERM(formula));
	res = msat_assert_formula(env,formula);
	assert(res == 0);
	
    }
    
    void newInterpreter::assertVariable()
    {
	string full_formula;

	
	for (iplist<BasicBlock>::iterator iter = func->getBasicBlockList().begin();
            iter != func->getBasicBlockList().end();
            iter++)
	{
	    
	    BasicBlock *basicblock = &(*iter);

	    ///assert active
	    if(basicblock->getNumUses() > 1)
	    {
		string s = "(assert (= $"+basicblock->getName().str()+" (or ";
		for(BasicBlock *pred : predecessors(basicblock))
		{
		    string transition_name = "$"+pred->getName().str()+"_"+basicblock->getName().str();
		    s = s + transition_name + " ";
		}
		s = s + ") ) )";
		outs()<<s<<'\n';
		full_formula = full_formula + s ;
	    }else if(basicblock->getNumUses() == 1)
	    {
		string s = "(assert (= $"+basicblock->getName().str()+" $"+basicblock->getSinglePredecessor()->getName().str()+"_"+basicblock->getName().str()+") )";
		outs()<<s<<'\n';
		full_formula = full_formula + s ;
	    }else if(basicblock->getNumUses()==0 && basicblock->getName().str()=="entry")
	    {
		string s = "(assert $entry)";
		outs()<<s<<'\n';
		full_formula = full_formula + s ;
	    }else
	    {
		outs()<<"the function has many entry...\n";
	    }
	    
	    
	    ///assert varible 
	    for(auto inst_i = basicblock->begin(),inst_e = basicblock->end();
		(inst_i != inst_e) && (!inst_i->isTerminator());
		inst_i++)
	    {
		switch(inst_i->getOpcode())
		{
		    case Instruction::Add:
		    {
			string s = "(assert (=> $"+basicblock->getName().str()+" (= $"+inst_i->getName().str()+" (bvadd ";
			string tail = ") ) ) )";
			s = s+ calculateVarible(inst_i->getOperand(0),inst_i->getOperand(1))+tail;
			full_formula = full_formula + s;
			outs()<<s<<'\n';
			break;
		    }
		    case Instruction::Sub:
		    {
			string s = "(assert (=> $"+basicblock->getName().str()+" (= $"+inst_i->getName().str()+" (bvsub ";
			string tail = " ) ) ) )";
			s = s+ calculateVarible(inst_i->getOperand(0),inst_i->getOperand(1))+tail;
			full_formula = full_formula + s;
			outs()<<s<<'\n';
			break;
		    }
		    case Instruction::Mul:
		    {
			string s = "(assert (=> $"+basicblock->getName().str()+" (= $"+inst_i->getName().str()+" (bvmul ";
			string tail = " ) ) ) )";
			s = s+ calculateVarible(inst_i->getOperand(0),inst_i->getOperand(1))+tail;
			full_formula = full_formula + s;
			outs()<<s<<'\n';
			break;
		    }
		    case Instruction::PHI:
		    {
			PHINode* phi = dyn_cast<PHINode>(inst_i);
			if(!phi)
			    break;
			
			unsigned int NumOperand = phi->getNumOperands();
			unsigned int NumForLoop = NumOperand-1;
			string s = "(assert (=> $"+basicblock->getName().str()+" (= $"+phi->getName().str()+" ";
			string tail = " ) ) )";
			
			for(unsigned int num =0;num < NumForLoop ;num++)
			{
			    s = s+"(ite $"+phi->getIncomingBlock(num)->getName().str()+"_"+basicblock->getName().str()+" "+calculateVarible(phi->getIncomingValue(num))+" ";
			    tail = tail+" )";
			}
			s = s + calculateVarible(phi->getIncomingValue(NumForLoop))+tail;
			full_formula = full_formula + s;
			outs()<<s<<'\n';
			break;
		    }
		    case Instruction::ICmp:
		    {
			
			ICmpInst *icmpInst = dyn_cast<ICmpInst>(inst_i);
			if(!icmpInst)
			{
			    break;
			}
			///deal the unsigned int comparation
			switch (icmpInst->getPredicate() )
			{
			    case CmpInst::ICMP_EQ:
			    {
				string s = "(assert (=> $"+basicblock->getName().str()+" (= $"+icmpInst->getName().str()+" (= "+calculateVarible(icmpInst->getOperand(0))+" "+calculateVarible(icmpInst->getOperand(1))+") ) ) )";
				full_formula = full_formula + s;
				outs()<<s<<'\n';
				break;
			    }
			    case CmpInst::ICMP_NE:
			    {
				string s = "(assert (=> $"+basicblock->getName().str()+" (= $"+icmpInst->getName().str()+" (not (= "+calculateVarible(icmpInst->getOperand(0))+" "+calculateVarible(icmpInst->getOperand(1))+") ) ) ) )";
				full_formula = full_formula + s;
				outs()<<s<<'\n';
				break;
			    }
			    case CmpInst::ICMP_UGT:
			    {
				string s = "(assert (=> $"+basicblock->getName().str()+" (= $"+icmpInst->getName().str()+" (bvugt "+calculateVarible(icmpInst->getOperand(0))+" "+calculateVarible(icmpInst->getOperand(1))+") ) ) )";
				full_formula = full_formula + s;
				outs()<<s<<'\n';
				break;
			    }
			    case CmpInst::ICMP_UGE:
			    {
				string s = "(assert (=> $"+basicblock->getName().str()+" (= $"+icmpInst->getName().str()+" (bvuge "+calculateVarible(icmpInst->getOperand(0))+" "+calculateVarible(icmpInst->getOperand(1))+") ) ) )";
				full_formula = full_formula + s;
				outs()<<s<<'\n';
				break;
			    }
			    case CmpInst::ICMP_ULT:
			    {
				string s = "(assert (=> $"+basicblock->getName().str()+" (= $"+icmpInst->getName().str()+" (bvult "+calculateVarible(icmpInst->getOperand(0))+" "+calculateVarible(icmpInst->getOperand(1))+") ) ) )";
				full_formula = full_formula + s;
				outs()<<s<<'\n';
				break;
			    }
			    case CmpInst::ICMP_ULE:
			    {
				string s = "(assert (=> $"+basicblock->getName().str()+" (= $"+icmpInst->getName().str()+" (bvule "+calculateVarible(icmpInst->getOperand(0))+" "+calculateVarible(icmpInst->getOperand(1))+") ) ) )";
				full_formula = full_formula + s;
				outs()<<s<<'\n';
				break;
			    }
			    case CmpInst::ICMP_SGT:
			    {
				string s = "(assert (=> $"+basicblock->getName().str()+" (= $"+icmpInst->getName().str()+" (bvsgt "+calculateVarible(icmpInst->getOperand(0))+" "+calculateVarible(icmpInst->getOperand(1))+") ) ) )";
				full_formula = full_formula + s;
				outs()<<s<<'\n';
				break;
			    }
			    case CmpInst::ICMP_SGE:
			    {
				string s = "(assert (=> $"+basicblock->getName().str()+" (= $"+icmpInst->getName().str()+" (bvsge "+calculateVarible(icmpInst->getOperand(0))+" "+calculateVarible(icmpInst->getOperand(1))+") ) ) )";
				full_formula = full_formula + s;
				outs()<<s<<'\n';
				break;
			    }
			    case CmpInst::ICMP_SLT:
			    {
				string s = "(assert (=> $"+basicblock->getName().str()+" (= $"+icmpInst->getName().str()+" (bvslt "+calculateVarible(icmpInst->getOperand(0))+" "+calculateVarible(icmpInst->getOperand(1))+") ) ) )";
				full_formula = full_formula + s;
				outs()<<s<<'\n';
				break;
			    }
			    case CmpInst::ICMP_SLE:
			    {
				string s = "(assert (=> $"+basicblock->getName().str()+" (= $"+icmpInst->getName().str()+" (bvsle "+calculateVarible(icmpInst->getOperand(0))+" "+calculateVarible(icmpInst->getOperand(1))+") ) ) )";
				full_formula = full_formula + s;
				outs()<<s<<'\n';
				break;
			    }
			    default:
			    {
				errs()<< "this Function "<<icmpInst->getName() <<" will be realize in the future ..."<< '\n';
			    }
			}
			break;
		    }
		    case Instruction::SExt:
		    {
			unsigned int lbitwidth = inst_i->getType()->getIntegerBitWidth();
			unsigned int rbitwidth = inst_i->getOperand(0)->getType()->getIntegerBitWidth();
			if(rbitwidth > 1)
			{
			    string s = "(assert (=> $"+basicblock->getName().str()+" (= $"+inst_i->getName().str()+"((_ sign_extend "+InttoString(lbitwidth-rbitwidth)+") "+calculateVarible(inst_i->getOperand(0))+"))))";
			    full_formula = full_formula + s;
			    outs()<<s<<'\n';
			    break;
			}else
			{
			    string s = "(assert (=> $"+basicblock->getName().str()+" (= $"+inst_i->getName().str()+"(ite "+calculateVarible(inst_i->getOperand(0))
					+" ((_ sign_extend "+InttoString(rbitwidth-lbitwidth)+") (_ bv1 1)) ((_ sign_extend "+InttoString(lbitwidth-rbitwidth)+") (_ bv0 1))))))";
			    full_formula = full_formula + s;
			    outs()<<s<<'\n';
			    break;
			}

// 			if(inst_i->getOperand(0)->getType()->getIntegerBitWidth() == 1)
// 			{
// 			    string s = "(assert (=> $"+basicblock->getName().str()+" (= $"+inst_i->getName().str()+" (ite $"+calculateVarible(inst_i->getOperand(0)) +" (_ bv1 64) (_ bv0 64) ) ) ) )";
// 			    assert_formula = assert_formula +s;
// // 			    outs()<<s<<'\n';
// 			    break;
// 			}else
// 			{
// 			    string s = "(assert (=> $"+basicblock->getName().str()+" (= $"+inst_i->getName().str()+" "+calculateVarible(inst_i->getOperand(0))+") ) )";
// 			    assert_formula = assert_formula +s;
// // 			    outs()<<s<<'\n';
// 			    break;
// 			}
		    }
		    case Instruction::ZExt:
		    {
			unsigned int lbitwidth = inst_i->getType()->getIntegerBitWidth();
			unsigned int rbitwidth = inst_i->getOperand(0)->getType()->getIntegerBitWidth();
			if(rbitwidth > 1)
			{
			    string s = "(assert (=> $"+basicblock->getName().str()+" (= $"+inst_i->getName().str()+"((_ zero_extend "+InttoString(lbitwidth-rbitwidth)+") "+calculateVarible(inst_i->getOperand(0))+"))))";
			    full_formula = full_formula + s;
			    outs()<<s<<'\n';
			    break;
			}else
			{
			    string s = "(assert (=> $"+basicblock->getName().str()+" (= $"+inst_i->getName().str()+"(ite "+calculateVarible(inst_i->getOperand(0))
					+" ((_ zero_extend "+InttoString(lbitwidth-rbitwidth)+") (_ bv1 1)) ((_ zero_extend "+InttoString(lbitwidth-rbitwidth)+") (_ bv0 1))))))";
			    full_formula = full_formula + s;
			    outs()<<s<<'\n';
			    break;
			}
// 			if(inst_i->getOperand(0)->getType()->getIntegerBitWidth() == 1)
// 			{
// 			    string s = "(assert (=> $"+basicblock->getName().str()+" (= $"+inst_i->getName().str()+" (ite "+calculateVarible(inst_i->getOperand(0)) +" (_ bv1 64) (_ bv0 64) ) ) ) )";
// 			    assert_formula = assert_formula +s;
// // 			    outs()<<s<<'\n';
// 			    break;
// 			}else
// 			{
// 			    string s = "(assert (=> $"+basicblock->getName().str()+" (= $"+inst_i->getName().str()+" "+calculateVarible(inst_i->getOperand(0))+") ) )";
// 			    assert_formula = assert_formula +s;
// // 			    outs()<<s<<'\n';
// 			    break;
// 			}
		    }
		    case Instruction::Trunc:
		    {
			unsigned int lbitwidth = inst_i->getType()->getIntegerBitWidth();
			unsigned int rbitwidth = inst_i->getOperand(0)->getType()->getIntegerBitWidth();
			if(lbitwidth == rbitwidth)
			{
			    outs()<<"this value trunc is invalid...\n";
			}
			if(lbitwidth > 1)
			{
			    string s = "(assert (=> $"+basicblock->getName().str()+" (= $"+inst_i->getName().str()+"((_ extract "+InttoString(lbitwidth-1)+" 0) "+calculateVarible(inst_i->getOperand(0))+"))))";
			    full_formula = full_formula + s;
			    outs()<<s<<'\n';
			    break;
			}else
			{
			    string s = "(assert (=> $"+basicblock->getName().str()+" (= $"+inst_i->getName().str()+"(ite (= ((_ extract 0 0) "+calculateVarible(inst_i->getOperand(0))+") #b1) true false))))";
			    full_formula = full_formula + s;
			    outs()<<s<<'\n';
			    break;
			}
// 			if(inst_i->getType()->getIntegerBitWidth() == 1)
// 			{
// 			    string s = "(assert (=> $"+basicblock->getName().str()+" (= $"+inst_i->getName().str()+" (ite (= "+calculateVarible(inst_i->getOperand(0))+" (_ bv0 64) ) true false) ) ) )";
// 			    assert_formula = assert_formula +s;
// // 			    outs()<<s<<'\n';
// 			    break;
// 			}else
// 			{
// 			    string s = "(assert (=> $"+basicblock->getName().str()+" (= $"+inst_i->getName().str()+" "+calculateVarible(inst_i->getOperand(0))+") ) )";
// 			    assert_formula = assert_formula +s;
// // 			    outs()<<s<<'\n';
// 			    break;
// 			}
		    }
		    case Instruction::BitCast:
		    {
			unsigned int lbitwidth = inst_i->getType()->getIntegerBitWidth();
			unsigned int rbitwidth = inst_i->getOperand(0)->getType()->getIntegerBitWidth();
			string s ;
			if(lbitwidth == rbitwidth)
			{
			    s = "(assert (=> $"+basicblock->getName().str()+" (= $"+inst_i->getName().str()+" "+calculateVarible(inst_i->getOperand(0))+" )))";
			}else
			{
			    outs()<<"this value BitCast is invalid...\n";
			}
			full_formula = full_formula + s;
			outs()<<s<<'\n';
			break;
		    }
		    case Instruction::AShr:
		    {
			string s = "(assert (=> $"+basicblock->getName().str()+" (= $"+inst_i->getName().str()+" (bvashr ";
			string tail = " ) ) ) )";
			s = s+ calculateVarible(inst_i->getOperand(0),inst_i->getOperand(1))+tail;
			full_formula = full_formula + s;
			outs()<<s+'\n';
			break;
		    }
		    case Instruction::LShr:
		    {
			string s = "(assert (=> $"+basicblock->getName().str()+" (= $"+inst_i->getName().str()+" (bvlshr ";
			string tail = " ) ) ) )";
			s = s+ calculateVarible(inst_i->getOperand(0),inst_i->getOperand(1))+tail;
			full_formula = full_formula + s;
			outs()<<s+'\n';
			break;
		    }
		    case Instruction::Shl:
		    {
			string s = "(assert (=> $"+basicblock->getName().str()+" (= $"+inst_i->getName().str()+" (bvshl ";
			string tail = " ) ) ) )";
			s = s+ calculateVarible(inst_i->getOperand(0),inst_i->getOperand(1))+tail;
			full_formula = full_formula + s;
			outs()<<s+'\n';
			break;
		    }
		    case Instruction::Xor:
		    {
			string s = "(assert (=> $"+basicblock->getName().str()+" (= $"+inst_i->getName().str()+" (bvxor ";
			string tail = " ) ) ) )";
			s = s+ calculateVarible(inst_i->getOperand(0),inst_i->getOperand(1))+tail;
			full_formula = full_formula + s;
			outs()<<s+'\n';
			break;
		    }
		    case Instruction::Or:
		    {
			string s = "(assert (=> $"+basicblock->getName().str()+" (= $"+inst_i->getName().str()+" (bvor ";
			string tail = " ) ) ) )";
			s = s+ calculateVarible(inst_i->getOperand(0),inst_i->getOperand(1))+tail;
			full_formula = full_formula + s;
			outs()<<s+'\n';
			break;
		    }
		    case Instruction::And:
		    {
			string s = "(assert (=> $"+basicblock->getName().str()+" (= $"+inst_i->getName().str()+" (bvand ";
			string tail = " ) ) ) )";
			s = s+ calculateVarible(inst_i->getOperand(0),inst_i->getOperand(1))+tail;
			full_formula = full_formula + s;
			outs()<<s+'\n';
			break;
		    }
		    case Instruction::SRem:
		    {
			string s = "(assert (=> $"+basicblock->getName().str()+" (= $"+inst_i->getName().str()+" (bvsrem ";
			string tail = " ) ) ) )";
			s = s+ calculateVarible(inst_i->getOperand(0),inst_i->getOperand(1))+tail;
			full_formula = full_formula + s;
			outs()<<s+'\n';
			break;
		    }
		    case Instruction::URem:
		    {
			string s = "(assert (=> $"+basicblock->getName().str()+" (= $"+inst_i->getName().str()+" (bvurem ";
			string tail = " ) ) ) )";
			s = s+ calculateVarible(inst_i->getOperand(0),inst_i->getOperand(1))+tail;
			full_formula = full_formula + s;
			outs()<<s+'\n';
			break;
		    }
		    case Instruction::SDiv:
		    {
			string s = "(assert (=> $"+basicblock->getName().str()+" (= $"+inst_i->getName().str()+" (bvsdiv ";
			string tail = " ) ) ) )";
			s = s+ calculateVarible(inst_i->getOperand(0),inst_i->getOperand(1))+tail;
			full_formula = full_formula + s;
			outs()<<s+'\n';
			break;
		    }
		    case Instruction::UDiv:
		    {
			string s = "(assert (=> $"+basicblock->getName().str()+" (= $"+inst_i->getName().str()+" (bvudiv ";
			string tail = " ) ) ) )";
			s = s+ calculateVarible(inst_i->getOperand(0),inst_i->getOperand(1))+tail;
			full_formula = full_formula + s;
			outs()<<s+'\n';
			break;
		    }
		    case Instruction::Call:
		    {
			const CallInst *callInst = cast<CallInst>(inst_i);
			ImmutableCallSite cs(callInst);
			auto callTgt = cs.getCalledFunction();
			string func_name = callTgt->getName().str();
			if(callTgt->isDeclaration())
			{
			    if(func_name.find("__VERIFIER_nondet",0) == 0)
			    {
				
			    }else if(func_name.find("__VERIFIER_assert",0) == 0)
			    {
				Value* arg = cast<Value>(cs.arg_begin()) ;
				string s;
// 				const string bbName = "$"+basicblock->getName().str();
// 				const string argName = "$"+arg->getName().str();
// 				s = s+" (and "+bbName+" (= "+argName+" (_ bv0 "+InttoString(arg->getType()->getIntegerBitWidth())+")))";
				s = "(and $"+basicblock->getName().str()+"(=> $"+basicblock->getName().str()+" (= $"+arg->getName().str()+" (_ bv0 "+InttoString(arg->getType()->getIntegerBitWidth())+"))))";
				latch_cond_formula = latch_cond_formula + s;
				end_formula = end_formula +"$"+basicblock->getName().str()+" ";
// 				outs()<<s+'\n';
// 				verify_formula = verify_formula + s;
// 				assert_cond.push_back(bbName);
// 				assert_cond.push_back(argName);
			    }else if(func_name.find("__VERIFIER_assume",0) == 0)
			    {
				Value* arg = cast<Value>(cs.arg_begin()) ;
				string s;
				s = s+"(assert (and $"+basicblock->getName().str()+" (= "+calculateVarible(arg)+" (_ bv1 "+InttoString(arg->getType()->getIntegerBitWidth())+"))))";
				full_formula = full_formula + s;
				outs()<<s+'\n';
				
			    }else
			    {
				outs()<<"this extend function is not defined\n";
			    }
			}else
			{
			    outs()<<"this function is not extend function, and neet to use inline pass\n";
			}
		    }
		}
		
	    }

	    
	    ///assert transition
	    unsigned int numSucc = basicblock->getTerminator()->getNumSuccessors();
	    switch(basicblock->getTerminator()->getOpcode())
	    {
		case Instruction::Switch:
		{
		    SwitchInst* swInst = cast<SwitchInst>(basicblock->getTerminator());
		    BasicBlock *Dest = swInst->getDefaultDest();
		    string Default_name = Dest->getName().str();
		    Value* Cond = swInst->getCondition();
		    string Cond_str = calculateVarible(Cond);
		    string bbi_name = basicblock->getName().str();
		    unsigned int n = swInst->getNumCases();
		    string default_subStr = "(and ";
		    string s = "(assert (and ";
		    // for(SwitchInst::CaseIt i = swInst->case_begin(),e = swInst->case_end(); i != e; i++)
		    // {
			// string constant = InttoString(i.getCaseValue()->getZExtValue());
			// string succ_name = i.getCaseSuccessor()->getName().str();
			// s = s + "(= (and (= "+Cond_str+" "+constant+") $"+bbi_name+") $"+bbi_name+"_"+succ_name+")";
			// default_subStr = default_subStr +"(not (= "+Cond_str+" "+constant+") ) ";
		    // }
			for(unsigned int num=0; num<swInst->getNumCases() ;num++)
		    {
				auto Case = *SwitchInst::ConstCaseIt::fromSuccessorIndex(swInst, num);
				string constant = InttoString(Case.getCaseValue()->getZExtValue());
				string succ_name = swInst->getSuccessor(num)->getName().str();
				s = s + "(= (and (= "+Cond_str+" "+constant+") $"+bbi_name+") $"+bbi_name+"_"+succ_name+")";
				default_subStr = default_subStr +"(not (= "+Cond_str+" "+constant+") ) ";
		    }
		    default_subStr = default_subStr + ")";
		    s = s + "(= (and $"+bbi_name+" "+default_subStr+" ) $"+bbi_name+"_"+Default_name+") ) )";
		    full_formula = full_formula +s;
		    outs()<<s+'\n';
		    break;
		}
		case Instruction::Br:
		{
		    BranchInst* brInst = cast<BranchInst>(basicblock->getTerminator());
		    string s;
		    if(numSucc==1)
		    {
			if(latch != basicblock)
			{
			    string bbi_name = basicblock->getName().str();
			    string bbsucc_name = basicblock->getTerminator()->getSuccessor(0)->getName().str();
			    s =s+ "(assert (= $"+bbi_name+" $"+bbi_name+"_"+bbsucc_name+") )";
			    full_formula = full_formula +s;
			    outs()<<s+'\n';
			}else
			{
			    full_formula = full_formula +Transition_latch_exit;
// 			    outs()<<latch_cond_formula<<'\n';
			    outs()<<Transition_latch_exit<<'\n';
			}
			
		    }else
		    {
			string bbi_name = basicblock->getName().str();
			string bbsucc1_name = basicblock->getTerminator()->getSuccessor(0)->getName().str();
			string bbsucc2_name = basicblock->getTerminator()->getSuccessor(1)->getName().str();
			s =s+ "(assert (and "+
				"(= (and $"+bbi_name+" "+calculateVarible(brInst->getCondition())+") $"+bbi_name+"_"+bbsucc1_name+")"+
				"(= (and $"+bbi_name+" (not "+calculateVarible(brInst->getCondition())+") ) $"+bbi_name+"_"+bbsucc2_name+") ) )";
			full_formula = full_formula +s;
			outs()<<s+'\n';
		    }
		    break;
		}
		case Instruction::Ret:
		{
// 		    string s;
// 		    if(!end_formula.empty())
// 		    {
// 			s = s + "(assert (=> (not (or "+end_formula+"))(not $"+basicblock->getName().str()+")))";
// 		    }else
// 		    {
// 			s = s + "(assert (ite $"+basicblock->getName().str()+" false true))";
// 		    }
// 		    full_formula = full_formula +s;
// 		    outs()<<s+'\n';
/*		    string s = "(assert $"+basicblock->getName().str()+" )";
		    full_formula = full_formula +s;
		    outs()<<s+'\n'*/;
		}
	    }

	}
	
	
	
// 	outs()<<verify_formula<<'\n';
// 	outs()<<status_assert<<'\n';
	latch_cond_formula = "(assert (or "+latch_cond_formula+"))";
	outs()<<latch_cond_formula<<'\n';
	full_formula = full_formula + latch_cond_formula;
	const char *k = full_formula.c_str();
	formula = msat_from_smtlib2(env,k);
	assert(!MSAT_ERROR_TERM(formula));
	res = msat_assert_formula(env,formula);
	assert(res == 0);
	

    }
    
    ///change llvm::Value to std::string
    string newInterpreter::calculateVarible(Value *v )
    {
	string s;
	if(auto cv1 = dyn_cast<Constant>(v))
	{
	    s = calculateConstant(cv1)+" ";
	}else
	{
	    s = "$"+ v->getName().str()+" ";
	}
	return s;
    }
    
    ///change llvm::Value to std::string
    string newInterpreter::calculateVarible(Value *v1 , Value *v2)
    {
	string s;
	if(auto cv1 = dyn_cast<Constant>(v1))
	{
	    s = calculateConstant(cv1)+" ";
	}else
	{
	    s = "$"+v1->getName().str()+" ";
	}
	if(auto cv2 = dyn_cast<Constant>(v2))
	{
	    s = s+calculateConstant(cv2);
	}else
	{
	    s = s+"$"+v2->getName().str();
	}
	return s;
    }
    
    ///change llvm::Constant to std::string 
    string newInterpreter::calculateConstant(Constant *cv)
    {
	string s;
	if(cv->getValueID() == Value::ConstantIntVal )
	{
	    ConstantInt *cInt = cast<ConstantInt>(cv);
	    unsigned int intvalue = cInt->getSExtValue();
	    if(cv->getType()->getIntegerBitWidth() != 1)
	    {
		s = "(_ bv"+InttoString(intvalue)+" "+InttoString(cv->getType()->getIntegerBitWidth())+")";
	    }else
	    {
		bool b = (bool)intvalue;
		if(b)
		{
		    s = "true";
		}else
		{
		    s = "false";
		}
	    }
// 	    outs()<<"\n"<<intvalue<<'\n';
	    
	}else
	{
	    outs()<<"\n;this type of constant had not defined in this function ...\n";
	}
	return s;
    }
    
    ///change Integer to std::string
    string newInterpreter::InttoString(unsigned int v)
    {
	string s;
	std::stringstream ss;
	ss << v;
	ss >> s;
	return s;
    }
    
