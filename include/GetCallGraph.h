#ifndef GETCALLGRAPH_H
#define GETCALLGRAPH_H






class CallSiteWrapper {
public:
  unsigned int id;
  Instruction *inst;
  string func;
  string file;
  string dir;
  unsigned int line;
  unsigned int calltimes;
  
  CallSiteWrapper(unsigned int _id, Instruction* I, StringRef _func, StringRef _file,
		  StringRef _dir, unsigned int _line, unsigned int _calltimes){
    id = _id;
    inst = I;
    func = _func.str();
    file = _file.str();
    dir = _dir.str();
    line = _line;
    calltimes = _calltimes;
  }
};



class FidSize {
 public:
  string fname;
  int fid;
  int icount;

  FidSize(string _fname, int _fid, int _icount){
    fname = _fname;
    fid = _fid;
    icount = _icount;
  }
};


/*
class CallEdge {
public:
  
	
};

*/





const vector<string> sshfiles = {
  "ssh.c.gcov.calltimesonly",
  "fake1.c.gcov.calltimesonly",
  "fake2.c.gcov.calltimesonly"
};





#endif //GETCALLGRAPH_H
