#ifndef DSA_DEBUG_H
#define DSA_DEBUG_H
#include <execinfo.h>
#include <stdlib.h>
#include "llvm/Support/raw_ostream.h"
class DSADebug {
public:
    static void printStackTrace(){
        void *returnAddresses[500];
        int depth = backtrace(returnAddresses, sizeof returnAddresses / sizeof *returnAddresses);
        llvm::errs() << "stack depth = " << depth << "\n";
        char **symbols = backtrace_symbols(returnAddresses, depth);
        for (int i = 0; i < depth; ++i) {
            llvm::errs() << symbols[i] << "\n";
        }
        free(symbols);
    }
};

#endif
