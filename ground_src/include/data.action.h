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
//  Module:     mips\include\data.action.h
//  Authors:    S.Edelkamp, M.Helmert
// 
// ***********************************************************

#ifndef _DATA_ACTION_H
#define _DATA_ACTION_H

#include <algorithm>
#include <string>
#include <vector>
#include <map>
using namespace std;
#include<data.exploreStep.h>
#include<data.instantiation.h>

class LispEntity;
class Domain;
class Formula;
class SymbolicFact;
class ActionDescription;
class NumericalCondition;

/** symbolic action representation, intermediate data structure
    instantiations kept as a list
*/

class Action {
  enum {NORMAL,WHEN,FORALL} LABEL;  // separate whens-constructs from others
  Action(const Action &copy); // prevent copying
  Domain& domain;             // handle to domain
  string name;                // action name
  int label;                  // additional label
  int timed;                  // fixed time action (due to timed initials)
  double time;                // time of fixed time action 
  int parameterCount;         // number of parameters
  ActionDescription* actionDescription; 
  // if part of higher order function, e.g generated by when-constructs    

  vector <pair <int,SymbolicFact * > > preAdd, preDel, effAdd, effDel;
  // propositional part
  vector <pair <int,NumericalCondition* > > numPre, numEff;
  vector <pair <string, pair<int,Formula* > > > prefs;
  vector <pair <int,pair <Formula*,Formula* > > > ors,implies;
  // numerical information
  vector<Instantiation> instantiations;
  // list of instantiations
  vector<Action* > whens;

  void scanForConstantPredicates(map<string,int>& parameters, 
                                 vector<pair <int,LispEntity> >& le,
                                 vector<pair <int,LispEntity> >& preAddList);
  // scan to eliminate constant predicates, extends parameter list
  // does tackle one quantifier, general enough for benchmark problems
  friend void ExploreStep::initActionData(vector<Action *> &);
  vector<vector<SymbolicFact *> > preByMaxPar;
          // non-unary preconditions with a given maximum argument number
  vector<vector<int> > preconditionCount;
  vector<vector<int> > validArguments;
  vector<int> split(string instance);
public:
  Action(Domain &d);
  Action(Domain &d, LispEntity &le);
  Action(string n, Domain &d, ActionDescription* ad, 
         vector<pair <int,LispEntity> >& preAddList,
         vector<pair <int,LispEntity> >& preDelList,
         vector<pair <int,LispEntity> >& effAddList,
         vector<pair <int,LispEntity> >& effDelList, 
         vector<pair <int,LispEntity> >& numPreList,
         vector<pair <int,LispEntity> >& numEffList, 
         vector<pair <int,LispEntity> >& prefList, 
	 vector<Action*>& when,
         map<string,int>& param,
         int label);
  ~Action();

  string getName()   {return name;}
  string toString();
  string getfullString();

  int getDerived();
  int getTimed() { return timed;}
  void setTimed() { timed = 1; }

  double getTime() { return time;}
  void setTime(double t) { time = t; }
  ActionDescription* getActionDescription() {return actionDescription; } 
  void setActionDescription(ActionDescription* ad) { actionDescription = ad; } 
  vector<pair <int,SymbolicFact *> >& getAddPreconditions()  {return preAdd;}
  vector<pair <int,SymbolicFact *> >& getDelPreconditions()  {return preDel;}
  vector<pair <int,SymbolicFact *> >& getAddEffects()        {return effAdd;}
  vector<pair <int,SymbolicFact *> >& getDelEffects()        {return effDel;}
  vector<pair <string, pair <int,Formula *> > >& getPrefs()        {return prefs;}
  vector<pair <int,pair<Formula*,Formula*> > >& getOrs()     {return ors;}
  vector<pair <int,pair<Formula*,Formula*> > >& getImplies()   {return implies;}
  vector<pair <int,NumericalCondition *> >&
    getNumPreconditions() {return numPre;}
  vector<pair <int,NumericalCondition *> >&
    getNumEffects()  {return numEff;}
  vector<Action*>& getWhens() { return whens; }
  int setTypedParameters(map<string,int>& parameters, 
			 map<string, string>& actionT,
			 int l);
  int getParameterCount()                   { return parameterCount;}
  void setParameterCount(int i)                   { parameterCount = i;}
  int getLabel()                            { return label; }

  vector<SymbolicFact *> &getPreconditionsByMaxPar(int maxPar) {
    return preByMaxPar[maxPar];
  }
  bool decreasePreconditionCountdown(int parNo, int objNo) {
    if(--(preconditionCount[parNo][objNo]) == 0) {
      validArguments[parNo].push_back(objNo);
      return true;
    }
    return false;
  }
  vector<int> &getValidArguments(int parNo) {return validArguments[parNo];}
  bool isValidArgument(int parNo, int objNo) {
    return preconditionCount[parNo][objNo] == 0;}

  double getMaxOperators(int objNo) const;

  void logInstantiation(const Instantiation& inst) {
    instantiations.push_back(inst);
  }

  vector<Instantiation> &getInstantiations() {
    return instantiations;
  }
  void instantiateBody(vector<int>& trueHeads, 
               vector<int>& fluentHeads);

  void eraseDuplicates() {
    sort(instantiations.begin(),
	 instantiations.end(),
	 Instantiation::comparefun);
    vector<Instantiation>::iterator newEnd =
      unique(instantiations.begin(),
         instantiations.end(),
         Instantiation::equalfun);
    instantiations.erase(newEnd,instantiations.end());
  }
  void eraseNoops() {  
    vector<Instantiation>::iterator newEnd =
      remove_if(instantiations.begin(),
        instantiations.end(),
        Instantiation::noop);
    if (whens.size()>0) return;
    instantiations.erase(newEnd,instantiations.end());
    
  }
  void eraseConstants() {  
    vector<Instantiation>::iterator newEnd =
      remove_if(instantiations.begin(),
        instantiations.end(),
        Instantiation::hasConstants);
      
    instantiations.erase(newEnd,instantiations.end());
    
  }
};

#endif
