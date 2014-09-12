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
//  Module:     mips\src\data.mergedPredicate.cc
//  Authors:    S.Edelkamp, M.Helmert
// 
// ***********************************************************

#include <algorithm>

using namespace std;

#include <util.tools.h>

#include <data.domain.h>
#include <data.partPredicate.h>
#include <data.predicate.h>
#include <data.mergedPredicate.h>

MergedPredicate::MergedPredicate(Predicate &initPred, vector<int>& pars) {
  parCount = initPred.getParameterCount();
  mergedParCount = pars.size();
  vector<int> order;
  for (int i = 0; i < mergedParCount; i++)
    order.push_back(pars[i]);
  int parsIndex = 0;
  for(int i = 0; i < parCount; i++)
    if (i == order[parsIndex]) {
      parsIndex++;
    } else {
      order.push_back(i);
    }
  parts.push_back(PartPredicate(initPred, false, order));
}

void MergedPredicate::makeCanonical() {
  sort(parts.begin(), parts.end());
}

void MergedPredicate::pushPredicate(Predicate &p, vector<int> &order) {
  parts.push_back(PartPredicate(p, p.getParameterCount() != parCount, order));
}

void MergedPredicate::popPredicate() {
  parts.pop_back();
}

bool MergedPredicate::operator==(const MergedPredicate &comp) const {
  return parCount == comp.parCount && parts == comp.parts;
}

PartPredicate *MergedPredicate::findPredicate(Predicate &p) {
  for(int i = 0; i < parts.size(); i++)
    if(parts[i].predicate == &p)
      return &parts[i];
  return 0;
}

string MergedPredicate::toString() {
  string back = "Dumping merged predicate (parCount = "
    + ::makeString(parCount) + "; mergedParCount = "
    + ::makeString(mergedParCount) + ")\n";
  for(int i = 0; i < parts.size(); i++) {
    back += parts[i].toString() + "\n";
  }
  return back;
}

string MergedPredicate::toString2() const {
  string back = "Dumping merged predicate (parCount = "
    + ::makeString(parCount) + "; mergedParCount = "
    + ::makeString(mergedParCount) + ")\n";
  for(int i = 0; i < parts.size(); i++) {
    back += parts[i].toString2() + "\n";
  }
  return back;
}

vector<vector<int> > MergedPredicate::getFactGroups(int objectCount) const {
  vector<vector<int> > back;
  vector<int> group;
  //cout << toString2() << endl;
  group.reserve(objectCount * parts.size());
  for(vector<int> rawArgs = ::firstTuple(parCount - mergedParCount);
      !::lastTuple(rawArgs, objectCount); ::nextTuple(rawArgs, objectCount)) {
    group.clear();
    for(int i = 0; i < parts.size(); i++)
      parts[i].appendInstantiations(rawArgs, group, mergedParCount, objectCount);
    back.push_back(group);
  }
  /*for (int i = 0; i < back.size(); i++) {
    for (int j = 0; j < back[i].size(); j++) {
      cout << back[i][j] << " ";
    }
    cout << endl;
  }
  cout << endl;*/
  return back;
}
