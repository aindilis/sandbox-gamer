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
//  Module:     mips\src\data.partPredicate.cc
//  Authors:    S.Edelkamp, M.Helmert
// 
// ***********************************************************

using namespace std;

#include <data.domain.h>
#include <data.predicate.h>
#include <data.symbolicFact.h>
#include <data.partPredicate.h>
#include <util.tools.h>

bool PartPredicate::operator==(const PartPredicate &comp) const {
  return predicate == comp.predicate && nullState == comp.nullState
    && parOrder == comp.parOrder;
}

bool PartPredicate::operator<(const PartPredicate &comp) const {
  if(predicate != comp.predicate)
    //return (*predicate) < (*comp.predicate);
    return predicate < comp.predicate;
  if(nullState != comp.nullState)
    return nullState == false;
  return parOrder < comp.parOrder;
}

string PartPredicate::toString() {
  string back = predicate->getName();
  if(nullState)
    back += " (null state)";
  int object = 0;
  for(int i = 0; i < parOrder.size(); i++) {
    back += " " + ::makeString(parOrder[i]);
    if (parOrder[i] == 0) back += "(f)";
    else back += "(c)";
  }
  return back;
}

string PartPredicate::toString2() const {
  string back = predicate->getName();
  if(nullState)
    back += " (null state)";
  int object = 0;
  for(int i = 0; i < parOrder.size(); i++) {
    back += " " + ::makeString(parOrder[i]);
    if (parOrder[i] == 0) back += "(f)";
    else back += "(c)";
  }
  return back;
}

vector<int> PartPredicate::getOrderedArgList(SymbolicFact &eff) {
  // It holds that back permutated by parOrder equals eff.parameters and
  // the length of back equals the number of parameters of the
  // merged predicate; inserts -1 at the front for null states.
  // This allows comparing parameter lists of PartPredicates with
  // different parameter orders.

  int parCount = parOrder.size();
  vector<int> args;
  args.resize(parCount);
  if(nullState) {   // special tag for value field of null-state predicates
    int effParCount = eff.getArguments().size();
    for (int i = 0; i < parCount - effParCount; i++) {
      args[i] = -1;
    }
    for (int i = parCount - effParCount; i < parCount; i++)
      args[i] = eff.getArguments()[parOrder[i]];
  } else
    for(int i = 0; i < parCount; i++)
      args[i] = eff.getArguments()[parOrder[i]];
  return args;
}

void PartPredicate::appendInstantiations(vector<int> &rawArgs, vector<int> &group,
					 int mergedParCount, int objectCount) const {
  int code = predicate->getFactLowerBound();
  int maxcode = predicate->getFactUpperBound(objectCount);
  int nullVarCount = parOrder.size() - predicate->getParameterCount();
  int maxPower = parOrder.size() - 1;
  maxPower -= nullVarCount;
  for(int i = mergedParCount; i < parOrder.size(); i++) {
    if ((maxPower - parOrder[i]) < 0) {
      cout << "Warning: negative exponent!" << endl;
    }
    code += rawArgs[i - mergedParCount] * ::pow(objectCount, maxPower - parOrder[i]);
  }

  if(nullState && nullVarCount == mergedParCount) {
    group.push_back(code);
    return;
  }

  vector<int> mergedParams(mergedParCount - nullVarCount);
  vector<int> mults(mergedParCount - nullVarCount);
  int counter = 0;
  for (int i = 0; i < mergedParCount; i++) {
    if (parOrder[i] >= 0) {
      mergedParams[counter] = parOrder[i];
      if ((maxPower - parOrder[i]) < 0) {
	cout << "Warning: negative exponent!" << endl;
      }
      mults[counter] = ::pow(objectCount, maxPower - parOrder[i]);
      counter++;
    }
  }
  int maxCount = ::pow(objectCount, mergedParams.size());
  vector<int> currParams(mergedParams.size(), 0);
  for (int i = 0; i < maxCount; i++) {
    int finalCode = code;
    for (int j = 0; j < mergedParams.size(); j++) {
      finalCode += mults[j] * currParams[j];
    }
    group.push_back(finalCode);
    for (int j = 0; j < currParams.size(); j++) {
      if (currParams[j] < objectCount - 1) {
	currParams[j]++;
	break;
      }
      currParams[j] = 0;
    }
  }
}
