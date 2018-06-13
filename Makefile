
LLVM_CONFIG=/usr/local/bin/llvm-config

#LLVM_CONFIG=/usr/llvm-4.0/bin/llvm-config
#LLVM_CONFIG=/usr/llvm-3.9.0/bin/llvm-config
#LLVM_CONFIG=/usr/llvm-3.4.2/bin/llvm-config
#LLVM_CONFIG=/usr/llvm-3.3/bin/llvm-config
#LLVM_CONFIG=/usr/llvm-3.2/bin/llvm-config


INC_DIR =./include  
SRC_DIR =./src
BIN_DIR =./bin
OBJ_DIR =./obj
LIB_DIR =./DS-AA/lib


SRC = ${wildcard ${SRC_DIR}/*.cpp}
OBJ = ${patsubst %.cpp, $(OBJ_DIR)/%.o, ${notdir ${SRC}}}
LIB = ${LIB_DIR}/AssistDS/DSNodeEquivs.o ${LIB_DIR}/smack/SmackDSAAA.o ${LIB_DIR}/DSA/LLVMDataStructure.a ${LIB_DIR}/sos/DSAA.a

TARGET=main
BIN_TARGET=${BIN_DIR}/${TARGET}

CXX=`$(LLVM_CONFIG) --bindir`/clang++
CXXFLAGS=`$(LLVM_CONFIG) --cppflags` -fPIC -fno-rtti -g -O3 -Wno-deprecated -std=c++11 -I$(INC_DIR)
LDFLAGS=`$(LLVM_CONFIG) --ldflags` -fPIC

${BIN_TARGET} : ${OBJ}
	${CXX} -shared ${OBJ} ${LIB} -o pdg.so $(LDFLAGS)
#guarantee the objs will automatically be rebuilt once the source files changed.
.PHONY : $(OBJS) 

$(OBJ_DIR)/%.o : $(SRC_DIR)/%.cpp
#	echo "Compiling $< == S@"
	${CXX} -c ${CXXFLAGS} $< -o $@


clean:
	rm -f $(OBJ_DIR)/*.o
	rm -f pdg.so

