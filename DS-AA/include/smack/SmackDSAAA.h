#ifndef SMACK_DSA_AA_H
#define SMACK_DSA_AA_H

#include "llvm/IR/InstVisitor.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Module.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/Passes.h"
#include "llvm/ADT/EquivalenceClasses.h"
#include "dsa/DataStructure.h"
#include "dsa/DSGraph.h"
#include "assistDS/DSNodeEquivs.h"
#include "sos/DSA_AA.h"

using namespace llvm;

class MemcpyCollector : public llvm::InstVisitor<MemcpyCollector> {
private:
  llvm::DSNodeEquivs *nodeEqs;
  std::vector<const llvm::DSNode*> memcpys;

public:
  MemcpyCollector(llvm::DSNodeEquivs *neqs) : nodeEqs(neqs) { }

  void visitMemCpyInst(llvm::MemCpyInst& mci) {
    const llvm::EquivalenceClasses<const llvm::DSNode*> &eqs
      = nodeEqs->getEquivalenceClasses();
    const llvm::DSNode *n1 = eqs.getLeaderValue(
      nodeEqs->getMemberForValue(mci.getOperand(0)) );
    const llvm::DSNode *n2 = eqs.getLeaderValue(
      nodeEqs->getMemberForValue(mci.getOperand(1)) );

    bool f1 = false, f2 = false;
    for (unsigned i=0; i<memcpys.size() && (!f1 || !f2); i++) {
      f1 = f1 || memcpys[i] == n1;
      f2 = f2 || memcpys[i] == n2;
    }

    if (!f1) memcpys.push_back(eqs.getLeaderValue(n1));
    if (!f2) memcpys.push_back(eqs.getLeaderValue(n2));
  }

  std::vector<const llvm::DSNode*> getMemcpys() {
    return memcpys;
  }
};

class SmackDSAAA: public llvm::ModulePass, public llvm::AliasAnalysis
{
private:
    const llvm::DataLayout* dataLayout;
    TDDataStructures *TD;
    BUDataStructures *BU;
    DSNodeEquivs *nodeEqs;
    DSAAA *dsa_aa;

    std::vector<const llvm::DSNode*> staticInits;
    std::vector<const llvm::DSNode*> memcpys;
	//AliasResult andersenAlias(const llvm::Value* l1, const llvm::Value* l2);
    llvm::DSNode *getNode(const llvm::Value* v);
    bool isAlloced(const llvm::Value* v);
    bool isExternal(const llvm::Value* v);
    bool isSingletonGlobal(const llvm::Value *V);

    bool isMemcpyd(const llvm::DSNode* n);
    bool isStaticInitd(const llvm::DSNode* n);
    std::vector<const llvm::DSNode*> collectMemcpys(llvm::Module &M, MemcpyCollector* mcc);
    std::vector<const llvm::DSNode*> collectStaticInits(llvm::Module &M);
    bool equivNodes(const llvm::DSNode* n1, const llvm::DSNode* n2);
    unsigned getOffset(const Location* l);
    bool disjoint(const Location* l1, const Location* l2);
public:
	static char ID;

	// Interfaces of AliasAnalysis.
	AliasResult alias(const Location& l1, const Location& l2) override;
	void deleteValue(llvm::Value* v) override;
	void copyValue(llvm::Value* from, llvm::Value* to) override;
	bool pointsToConstantMemory(const Location& loc, bool orLocal) override;
	//ModRefResult getModRefInfo (llvm::ImmutableCallSite cs, const Location &loc);


	SmackDSAAA(): ModulePass(ID), TD(nullptr), BU(nullptr), dataLayout(nullptr) {}
	bool runOnModule(llvm::Module &M) override;
	void getAnalysisUsage(llvm::AnalysisUsage &AU) const override;
	void* getAdjustedAnalysisPointer(llvm::AnalysisID PI) override;

    llvm::DSGraph *getGraphForValue(const llvm::Value *V);

    const Function* getFunction(const Value* v);
};

#endif
