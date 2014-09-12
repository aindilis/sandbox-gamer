// ***********************************************************
// 
//  Book:       Heuristic Search
// 
//  Authors:    S.Edelkamp, S.Schroedl
// 
//  See file README for information on using and copying 
//  this software.
// 
//  Project:    Mips - model checking integrated planning
//              system
// 
//  Module:     mips\src\mips.cc
//  Authors:    S.Edelkamp, M.Helmert
// 
// ***********************************************************

#include <iostream>
#include <unistd.h>
#include <execinfo.h>
#include <signal.h>
#include <cstdlib>
#include <cstdio>


using namespace std;

#include <data.predicate.h>
#include <data.object.h>
#include <data.domain.h>
#include <util.options.h>
#include <util.tools.h>

#define TIMEOUT 7200


void handler(int sig) {
    void *array[10];
    size_t size;

    // get void*'s for all entries on the stack
    size = backtrace(array, 20);

    // print out all the frames to stderr
    fprintf(stderr, "Error: signal %d:\n", sig);
    backtrace_symbols_fd(array, size, 2);
    exit(1);
}


int main(int argc, char *argv[]) {

  signal(SIGSEGV, handler);   // install our handler
  // alarm(TIMEOUT);

  string domFile, probFile;
  ::options.read(argc, argv, domFile, probFile);
  Domain* dom = new Domain(domFile, probFile);
  return 0;
}
