#include "llvm/IR/Module.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/Passes.h"
#include "llvm/Support/raw_ostream.h"
#include <iostream>
using namespace llvm;


namespace {
    class DSAATest : public ModulePass, public AliasAnalysis {
private:
    const llvm::DataLayout* dataLayout;
public:
    static char ID;
    //DSAA() : ModulePass(ID) {}
    DSAATest() : ModulePass(ID), dataLayout(nullptr) {}
    ~DSAATest() {}
    bool runOnModule(Module &M) {
      InitializeAliasAnalysis(this);
      dataLayout = &(getAnalysis<DataLayoutPass>().getDataLayout());
      errs() << "runOnModule(Module &M) \n";
      return false;
    }



    void getAnalysisUsage(AnalysisUsage &AU) const override {
      errs() << "getAnalysisUsage(AnalysisUsage &AU) \n";
      AU.addRequired<AliasAnalysis>();
      AU.addRequired<DataLayoutPass>();
      AU.setPreservesAll();
    }
    AliasAnalysis::AliasResult alias(const Location &LocA, const Location &LocB) {
        std::cout << "alias(const Location &LocA, const Location &LocB) \n";
        errs() << "alias(const Location &LocA, const Location &LocB) \n";
        return NoAlias;
    }

    AliasResult alias(const Value *V1, uint64_t V1Size,
                     const Value *V2, uint64_t V2Size) {

        std::cout << "alias(const Value *V1, uint64_t V1Size, const Value *V2, uint64_t V2Size) \n";
        errs() << "alias(const Value *V1, uint64_t V1Size, const Value *V2, uint64_t V2Size) \n";
        return NoAlias;
   }

    uint64_t getTypeStoreSize(Type *Ty) {
       return UnknownSize;
    }

//    ModRefResult getModRefInfo(ImmutableCallSite CS,
//                               const Location &Loc) override;
//
//    ModRefResult getModRefInfo(ImmutableCallSite CS1,
//                               ImmutableCallSite CS2) override {
//      // The AliasAnalysis base class has some smarts, lets use them.
//      return AliasAnalysis::getModRefInfo(CS1, CS2);
//    }

    /// pointsToConstantMemory - Chase pointers until we find a (constant
    /// global) or not.
    //bool pointsToConstantMemory(const Location &Loc, bool OrLocal) override;

    /// Get the location associated with a pointer argument of a callsite.
    //Location getArgLocation(ImmutableCallSite CS, unsigned ArgIdx,
    //                        ModRefResult &Mask) override;

    /// getModRefBehavior - Return the behavior when calling the given
    /// call site.
    //ModRefBehavior getModRefBehavior(ImmutableCallSite CS) override;

    /// getModRefBehavior - Return the behavior when calling the given function.
    /// For use when the call site is not known.
    //ModRefBehavior getModRefBehavior(const Function *F) override;

    /// getAdjustedAnalysisPointer - This method is used when a pass implements
    /// an analysis interface through multiple inheritance.  If needed, it
    /// should override this to adjust the this pointer as needed for the
    /// specified pass info.
//    void *getAdjustedAnalysisPointer(const void *ID) override {
//      if (ID == &AliasAnalysis::ID)
//        return (AliasAnalysis*)this;
//      return this;
//    }
    };
} //end of anonymous namespace

    RegisterPass<DSAATest> X("my-ds-aa", "Data Structure Graph Based Alias Analysis - Test");
    RegisterAnalysisGroup<AliasAnalysis> Y(X);
    char DSAATest::ID = 0;

