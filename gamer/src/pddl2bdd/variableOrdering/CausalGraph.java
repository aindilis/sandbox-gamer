/*
 * Gamer, a tool for finding optimal plans
 * Copyright (C) 2007-2013 by Peter Kissmann
 * 
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 * 
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301, USA
 */

package pddl2bdd.variableOrdering;

import pddl2bdd.parser.GroundedPDDLParser;
import pddl2bdd.parser.logic.*;
import java.util.*;

/**
 *
 * @author Peter Kissmann
 * @version 2.0
 */
public class CausalGraph {
    private CausalGraphNode[] variables;
    private boolean removeDuplicates; 

    public CausalGraph(LinkedList<LinkedList<String>> partitions, boolean bidir, boolean removeDuplicates) {
        variables = new CausalGraphNode[partitions.size()];
        for (int i = 0; i < partitions.size(); i++) {
            variables[i] = new CausalGraphNode(i);
        }
        this.removeDuplicates = removeDuplicates;

        ListIterator<LinkedList<String>> partIt = partitions.listIterator();
        LinkedList<String> allVars = new LinkedList<String>();
        LinkedList<Integer> partitionIndices = new LinkedList<Integer>();
        while (partIt.hasNext()) {
            partitionIndices.add(allVars.size());
            allVars.addAll(partIt.next());
        }
        ListIterator<Action> actionIt = GroundedPDDLParser.actions.listIterator();
        while (actionIt.hasNext()) {
            Action currentAction = actionIt.next();
            HashSet<Integer> effIndices = new HashSet<Integer>();
            LinkedList<HashSet<Integer>> condPreIndices = new LinkedList<HashSet<Integer>>();
            LinkedList<HashSet<Integer>> condEffIndices = new LinkedList<HashSet<Integer>>();
            findAllVariables(effIndices, condPreIndices, condEffIndices, allVars, partitionIndices,
                             currentAction.getEffect(), false);
            HashSet<Integer> preIndices = new HashSet<Integer>();
            findAllVariables(preIndices, null, null, allVars, partitionIndices,
                             currentAction.getPrecondition(), false);
            Iterator<Integer> preIndicesIt;
            int preIndex;
            int effIndex;
            if (condPreIndices.size() == 0) {
                // no conditional effects present
                preIndicesIt = preIndices.iterator();
                while (preIndicesIt.hasNext()) {
                    preIndex = preIndicesIt.next();
                    Iterator<Integer> effIndicesIt = effIndices.iterator();
                    while (effIndicesIt.hasNext()) {
                        effIndex = effIndicesIt.next();
                        if (preIndex != effIndex) {
                            variables[preIndex].addSuccessor(variables[effIndex], removeDuplicates);
                            if (bidir)
                                variables[effIndex].addSuccessor(variables[preIndex], removeDuplicates);
                        }
                    }
                }
                preIndicesIt = effIndices.iterator();
                while (preIndicesIt.hasNext()) {
                    preIndex = preIndicesIt.next();
                    Iterator<Integer> effIndicesIt = effIndices.iterator();
                    while (effIndicesIt.hasNext()) {
                        effIndex = effIndicesIt.next();
                        if (preIndex != effIndex) {
                            variables[preIndex].addSuccessor(variables[effIndex], removeDuplicates);
                        }
                    }
                }
                if (bidir) {
                    preIndicesIt = preIndices.iterator();
                    while (preIndicesIt.hasNext()) {
                        preIndex = preIndicesIt.next();
                        Iterator<Integer> effIndicesIt = preIndices.iterator();
                        while (effIndicesIt.hasNext()) {
                            effIndex = effIndicesIt.next();
                            if (preIndex != effIndex) {
                                variables[preIndex].addSuccessor(variables[effIndex], removeDuplicates);
                            }
                        }
                    }
                }
            } else {
                // conditional effects exist
                HashSet<Integer> allEffIndices = new HashSet<Integer>(effIndices);
                ListIterator<HashSet<Integer>> condEffIt = condEffIndices.listIterator();
                while (condEffIt.hasNext()) {
                    HashSet<Integer> condEff = condEffIt.next();
                    allEffIndices.addAll(condEff);
                    /*ListIterator<Integer> condEffIndicesIt = condEff.listIterator();
                    while (condEffIndicesIt.hasNext()) {
                        Integer condEffIndex = condEffIndicesIt.next();
                        if (!allEffIndices.contains(condEffIndex)) {
                            allEffIndices.add(condEffIndex);
                        }
                    }*/
                }
                preIndicesIt = preIndices.iterator();
                while (preIndicesIt.hasNext()) {
                    // edge from pre to every (also cond.) effect
                    preIndex = preIndicesIt.next();
                    Iterator<Integer> effIndicesIt = allEffIndices.iterator();
                    while (effIndicesIt.hasNext()) {
                        effIndex = effIndicesIt.next();
                        if (preIndex != effIndex) {
                            variables[preIndex].addSuccessor(variables[effIndex], removeDuplicates);
                        }
                    }
                }
                preIndicesIt = effIndices.iterator();
                while (preIndicesIt.hasNext()) {
                    // edge from each normal effect to every (also cond.) effect
                    preIndex = preIndicesIt.next();
                    Iterator<Integer> effIndicesIt = allEffIndices.iterator();
                    while (effIndicesIt.hasNext()) {
                        effIndex = effIndicesIt.next();
                        if (preIndex != effIndex) {
                            variables[preIndex].addSuccessor(variables[effIndex], removeDuplicates);
                        }
                    }
                }
                ListIterator<HashSet<Integer>> condPreIt = condPreIndices.listIterator();
                condEffIt = condEffIndices.listIterator();
                while (condPreIt.hasNext()) {
                    // both lists must have same length
                    HashSet<Integer> condPre = condPreIt.next();
                    HashSet<Integer> condEff = condEffIt.next();
                    HashSet<Integer> normAndCondEffIndices = new HashSet<Integer>(effIndices);
                    normAndCondEffIndices.addAll(condEff);
                    /*ListIterator<Integer> condEffIndicesIt = condEff.listIterator();
                    while (condEffIndicesIt.hasNext()) {
                        effIndex = condEffIndicesIt.next();
                        if (!normAndCondEffIndices.contains(effIndex)) {
                            normAndCondEffIndices.add(effIndex);
                        }
                    }*/
                    Iterator<Integer> condPreIndicesIt = condPre.iterator();
                    while (condPreIndicesIt.hasNext()) {
                        // edge from cond. pre to normal and corresponding cond. effects
                        preIndex = condPreIndicesIt.next();
                        Iterator<Integer> condEffIndicesIt = normAndCondEffIndices.iterator();
                        while (condEffIndicesIt.hasNext()) {
                            effIndex = condEffIndicesIt.next();
                            if (preIndex != effIndex) {
                                variables[preIndex].addSuccessor(variables[effIndex], removeDuplicates);
                            }
                        }
                    }
                    condPreIndicesIt = condEff.iterator();
                    while (condPreIndicesIt.hasNext()) {
                        // edge from cond. eff to normal and corresponding cond. effects
                        preIndex = condPreIndicesIt.next();
                        Iterator<Integer> condEffIndicesIt = normAndCondEffIndices.iterator();
                        while (condEffIndicesIt.hasNext()) {
                            effIndex = condEffIndicesIt.next();
                            if (preIndex != effIndex) {
                                variables[preIndex].addSuccessor(variables[effIndex], removeDuplicates);
                            }
                        }
                    }
                }
                if (bidir) {
                    HashSet<Integer> allPreIndices = new HashSet<Integer>(preIndices);
                    condPreIt = condPreIndices.listIterator();
                    while (condPreIt.hasNext()) {
                        HashSet<Integer> condPre = condPreIt.next();
                        allPreIndices.addAll(condPre);
                        /*ListIterator<Integer> condPreIndicesIt = condPre.listIterator();
                        while (condPreIndicesIt.hasNext()) {
                            Integer condPreIndex = condPreIndicesIt.next();
                            if (!allPreIndices.contains(condPreIndex)) {
                                allPreIndices.add(condPreIndex);
                            }
                        }*/
                    }
                    preIndicesIt = preIndices.iterator();
                    while (preIndicesIt.hasNext()) {
                        // edge from each normal precondition to every (also cond.) precondition
                        preIndex = preIndicesIt.next();
                        Iterator<Integer> effIndicesIt = allPreIndices.iterator();
                        while (effIndicesIt.hasNext()) {
                            effIndex = effIndicesIt.next();
                            if (preIndex != effIndex) {
                                variables[preIndex].addSuccessor(variables[effIndex], removeDuplicates);
                            }
                        }
                    }
                    preIndicesIt = effIndices.iterator();
                    while (preIndicesIt.hasNext()) {
                        // edge from each normal effect to every (also cond.) effect
                        preIndex = preIndicesIt.next();
                        Iterator<Integer> effIndicesIt = allPreIndices.iterator();
                        while (effIndicesIt.hasNext()) {
                            effIndex = effIndicesIt.next();
                            if (preIndex != effIndex) {
                                variables[preIndex].addSuccessor(variables[effIndex], removeDuplicates);
                            }
                        }
                    }
                    condPreIt = condPreIndices.listIterator();
                    condEffIt = condEffIndices.listIterator();
                    while (condPreIt.hasNext()) {
                        // both lists must have same length
                        HashSet<Integer> condPre = condPreIt.next();
                        HashSet<Integer> condEff = condEffIt.next();
                        HashSet<Integer> normAndCondPreIndices = new HashSet<Integer>(preIndices);
                        normAndCondPreIndices.addAll(condPre);
                        /*ListIterator<Integer> condPreIndicesIt = condPre.listIterator();
                        ListIterator<Integer> condEffIndicesIt;
                        while (condPreIndicesIt.hasNext()) {
                            preIndex = condPreIndicesIt.next();
                            if (!normAndCondPreIndices.contains(preIndex)) {
                                normAndCondPreIndices.add(preIndex);
                            }
                        }*/
                        Iterator<Integer> condPreIndicesIt = condPre.iterator();
                        while (condPreIndicesIt.hasNext()) {
                            // edge from cond. pre to normal and corresponding cond. effects
                            preIndex = condPreIndicesIt.next();
                            Iterator<Integer> condEffIndicesIt = normAndCondPreIndices.iterator();
                            while (condEffIndicesIt.hasNext()) {
                                effIndex = condEffIndicesIt.next();
                                if (preIndex != effIndex) {
                                    variables[preIndex].addSuccessor(variables[effIndex], removeDuplicates);
                                }
                            }
                        }
                        condPreIndicesIt = condEff.iterator();
                        while (condPreIndicesIt.hasNext()) {
                            // edge from cond. eff to normal and corresponding cond. effects
                            preIndex = condPreIndicesIt.next();
                            Iterator<Integer> condEffIndicesIt = normAndCondPreIndices.iterator();
                            while (condEffIndicesIt.hasNext()) {
                                effIndex = condEffIndicesIt.next();
                                if (preIndex != effIndex) {
                                    variables[preIndex].addSuccessor(variables[effIndex], removeDuplicates);
                                }
                            }
                        }
                    }
                }
            }
        }

        for (int i = 0; i < variables.length; i++) {
            variables[i].sort();
        }
    }

    private void findAllVariables(HashSet<Integer> allIndices, LinkedList<HashSet<Integer>> condPreIndices,
                                  LinkedList<HashSet<Integer>> condEffIndices, LinkedList<String> allVariables,
                                  LinkedList<Integer> indices, Expression formula, boolean inCondition) {
        formula.getClass();
        if (formula instanceof AndOrTerm) {
            ListIterator<Expression> termIt = ((AndOrTerm) formula).getTerms()
                    .listIterator();
            while (termIt.hasNext()) {
                findAllVariables(allIndices, condPreIndices, condEffIndices, allVariables, indices, termIt.next(), inCondition);
            }
        } else if (formula instanceof NotTerm) {
            findAllVariables(allIndices, condPreIndices, condEffIndices, allVariables, indices,
                             ((NotTerm) formula).getTerm(), inCondition);
        } else if (formula instanceof Predicate) {
            if (!((Predicate) formula).getName().equalsIgnoreCase("foo")) {
                int index = allVariables.indexOf(((Predicate) formula)
                        .getName());
                ListIterator<Integer> indicesIt = indices.listIterator();
                int partIndex = -1;
                while (indicesIt.hasNext()) {
                    if (indicesIt.next() > index)
                        break;
                    partIndex++;
                }
                //if (!allIndices.contains(partIndex)) {
                allIndices.add(partIndex);
                //}
            }
        } else if (formula instanceof Condition) {
            HashSet<Integer> condPres = new HashSet<Integer>();
            findAllVariables(condPres, condPreIndices, condEffIndices, allVariables, indices,
                             ((Condition) formula).getPre(), true);
            condPreIndices.add(condPres);
            HashSet<Integer> condEffs = new HashSet<Integer>();
            findAllVariables(condEffs, condPreIndices, condEffIndices, allVariables, indices,
                             ((Condition) formula).getEff(), true);
            condEffIndices.add(condEffs);
        } else {
            System.err.println("Error: class " + formula.getClass()
                    + " in findAllVariables!");
            System.err.println("Expression was:");
            System.err.println(formula);
            System.exit(1);
        }
    }

    public int getNumberOfVariables() {
    	return variables.length;
    }

    public CausalGraphNode getVariable(int index) {
        return variables[index];
    }

    public void addEdge(int u, int v) {
        variables[u].addSuccessor(variables[v], removeDuplicates);
    }

    public String toString() {
        String out = "";
        for (int i = 0; i < variables.length; i++) {
            out += variables[i] + "\n";
        }
        return out;
    }
}
