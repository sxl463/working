#ifndef DSA_AA_H
#define DSA_AA_H

#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Module.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/Passes.h"
#include "dsa/DataStructure.h"
#include "dsa/DSGraph.h"
using namespace llvm;

class DSAAA: public llvm::ModulePass, public llvm::AliasAnalysis
{
private:
	const llvm::DataLayout* dataLayout;
    TDDataStructures *TD;
    BUDataStructures *BU;

    // These members are used to cache mod/ref information to make us return
    // results faster, particularly for aa-eval.  On the first request of
    // mod/ref information for a particular call site, we compute and store the
    // calculated nodemap for the call site.  Any time DSA info is updated we
    // free this information, and when we move onto a new call site, this
    // information is also freed.
    CallSite MapCS;
    std::multimap<DSNode*, const DSNode*> CallerCalleeMap;

    DSGraph *getGraphForValue(const Value *V);
public:
    std::set<DSNode*> DEBUG_IncompleteNodeSet;
    std::set<std::string> DEBUG_QueryFunctionSet;
	static char ID;

	// Interfaces of AliasAnalysis.
	AliasResult alias(const Location& l1, const Location& l2) override;
	void deleteValue(llvm::Value* v) override;
	void copyValue(llvm::Value* from, llvm::Value* to) override;
	bool pointsToConstantMemory(const Location& loc, bool orLocal) override;
	//ModRefResult getModRefInfo (llvm::ImmutableCallSite cs, const Location &loc);

	DSAAA(): ModulePass(ID), TD(nullptr), BU(nullptr), dataLayout(nullptr) {}
	~DSAAA() {
        InvalidateCache();
	}
	void InvalidateCache() {
      MapCS = CallSite();
      CallerCalleeMap.clear();
    }
	bool runOnModule(llvm::Module &M) override;
	void getAnalysisUsage(llvm::AnalysisUsage &AU) const override;
	void* getAdjustedAnalysisPointer(llvm::AnalysisID PI) override;
};

#endif
