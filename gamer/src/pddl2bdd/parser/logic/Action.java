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

package pddl2bdd.parser.logic;

import java.util.*;

import pddl2bdd.util.Maths;
import pddl2bdd.variableOrdering.*;

import net.sf.javabdd.*;

/**
 * @author Peter Kissmann
 * @version 2.0
 */
public class Action {
	public Action() {
		unused = false;
	}

	/*
	 * for (int i = 0; i < topActionNode.numNodes(); i++) { PNode action =
	 * topActionNode.getNode(i); if
	 * (action.getToken().token.equals(":multi-action")) continue; PNode effect
	 * = action.getNode(2); if (!effect.getToken().token.equals("and"))
	 * continue; HashMap<String, PNode> addEffects = new HashMap<String,
	 * PNode>(); HashMap<String, PNode> delEffects = new HashMap<String,
	 * PNode>(); for (int j = 0; j < effect.numNodes(); j++) { PNode node =
	 * effect.getNode(j); if (((TypeClass)
	 * node.getToken().type).equals(TypeClass.NOT)) { PNode node2 =
	 * node.getNode(0); if (!((TypeClass)
	 * node2.getToken().type).equals(TypeClass.NAME))
	 * System.err.println("Warning! Unexpected token in deleteAddAndDeleteEffects"
	 * ); delEffects.put(node2.getToken().token, node); } else if (((TypeClass)
	 * node.getToken().type).equals(TypeClass.NAME)) {
	 * addEffects.put(node.getToken().token, node); } else
	 * System.err.println("Warning! Unexpected token in deleteAddAndDeleteEffects"
	 * ); } Iterator<String> delEffectsIt = delEffects.keySet().iterator();
	 * while (delEffectsIt.hasNext()) { String effectName = delEffectsIt.next();
	 * if (addEffects.containsKey(effectName)) delEffectsIt.remove(); } int
	 * newSize = addEffects.size() + delEffects.size(); if (newSize <
	 * effect.numNodes()) { PNode newEffect = new PNode(newSize);
	 * newEffect.setToken(effect.getToken()); int counter = 0; for (PNode node :
	 * addEffects.values()) { // System.out.println(node.getToken().token);
	 * newEffect.setNode(counter++, node); } for (PNode node :
	 * delEffects.values()) { // System.out.println(node.getToken().token);
	 * newEffect.setNode(counter++, node); } // System.out.println();
	 * action.setNode(2, newEffect); } }
	 */

	public BDD createBDD(BDDFactory factory, LinkedList<String> nAryVariables,
                         LinkedList<BDD> nAryVariablesPreBDDs,
                         LinkedList<BDD> nAryVariablesEffBDDs,
                         LinkedList<LinkedList<String>> partitionedVariables,
                         BDD[] variables, boolean[] unusedVarIndices) {
        //System.out.println(" ... for action " + name);
        //BDD tmp1;
        //BDD tmp2;
		BDD preBDD = precondition.createBDD(factory, nAryVariables,
                                            nAryVariablesPreBDDs, nAryVariablesEffBDDs, true, unusedVarIndices);
		if (preBDD == null)
			preBDD = factory.one();
        
	// 	tmp2 = effect.createBDD(factory, nAryVariables, nAryVariablesPreBDDs, nAryVariablesEffBDDs, false, unusedVarIndices);
	// 	if (tmp2 == null) {
	// 		preBDD.free();
	// 		return null;
	// 	}
	// 	action = preBDD.and(tmp2);
    //     System.out.print("action: ");
    //     action.printSet();
	// 	tmp2.free();
	// 	Vector<String> addEffects = new Vector<String>();
	// 	Vector<String> delEffects = new Vector<String>();
    //     Vector<Condition> condEffects = new Vector<Condition>();
    //     Vector<Vector<String>> condEffectVars = new Vector<Vector<String>>();
	// 	effect.classifyEffects(addEffects, delEffects, condEffects, condEffectVars, false, false);
	// 	int partitionCounter = 0;
	// 	int currentVariable = 0;
	// 	ListIterator<LinkedList<String>> partitionIt = partitionedVariables
	// 			.listIterator();
    //     System.out.println(name);
	// 	while (partitionIt.hasNext()) {
	// 		LinkedList<String> group = partitionIt.next();
	// 		int size = group.size();
	// 		int numberOfVars = Maths.log2(size);
	// 		boolean oneVariableInserted = false;
	// 		boolean positiveVariableInserted = false;
    //         boolean inConditionalEffect = false;
	// 		ListIterator<String> groupIt = group.listIterator();
	// 		while (groupIt.hasNext()) {
	// 			String pred = groupIt.next();
	// 			if (addEffects.contains(pred)) {
	// 				oneVariableInserted = true;
	// 				positiveVariableInserted = true;
    //                 // cannot be a positive effect and in some conditional effect
    //                 // thus, safe to break here
	// 				break;
	// 			}
	// 			if (!oneVariableInserted && delEffects.contains(pred))
	// 				oneVariableInserted = true;
    //             ListIterator<Vector<String>> condEffIt = condEffectVars.listIterator();
    //             while (condEffIt.hasNext()) {
    //                 Vector<String> condEff = condEffIt.next();
    //                 if (condEff.contains(pred)) {
    //                     inConditionalEffect = true;
    //                     break;
    //                 }
    //             }
    //             if (inConditionalEffect)
    //                 // cannot be a positive effect and in some conditional effect
    //                 // thus, safe to break here
    //                 break;
	// 		}
    //         System.out.println("one: " + oneVariableInserted + "; pos: " + positiveVariableInserted + "; cond: " + inConditionalEffect);
    //         if (inConditionalEffect) {
    //             //System.out.println("group " + partitionCounter + " appears in cond. effect.");
    //             BDD cond = factory.one();
    //             int condId = 0;
    //             ListIterator<Vector<String>> condEffIt = condEffectVars.listIterator();
    //             while (condEffIt.hasNext()) {
    //                 Vector<String> condEff = condEffIt.next();
    //                 groupIt = group.listIterator();
    //                 boolean condContainsVar = false;
    //                 while (groupIt.hasNext()) {
    //                     String pred = groupIt.next();
    //                     if (condEff.contains(pred)) {
    //                         condContainsVar = true;
    //                         System.out.println("var " + pred + " in condEffect " + condId);
    //                         break;
    //                     }
    //                 }
    //                 if (condContainsVar) {
    //                     Condition condition = condEffects.get(condId);
    //                     tmp1 = condition.createPreBDD(factory, nAryVariables, nAryVariablesPreBDDs, unusedVarIndices); // cond-pre
    //                     tmp2 = tmp1.not();
    //                     tmp1.free();
    //                     tmp1 = cond;
    //                     cond = tmp1.and(tmp2);
    //                     tmp1.free();
    //                     tmp2.free();
    //                 }
    //                 condId++;
    //             }
    //             /*BDD fullCond = factory.one();
    //             for (int i = 0; i < numberOfVars; i++) {
	// 				tmp1 = variables[(currentVariable + i) * 2];
    //                 tmp1 = tmp1.biimp(variables[(currentVariable + i) * 2 + 1]);
    //                 tmp2 = cond.and(tmp1);
	// 				//tmp1 = tmp2.biimp(variables[(currentVariable + i) * 2 + 1]);
    //                 tmp1.free();
    //                 tmp1 = fullCond;
    //                 fullCond = tmp1.and(tmp2);
    //                 tmp1.free();
    //                 tmp2.free();


    //                 /*tmp2 = tmp1.and(cond);
    //                 tmp1.free();
    //                 tmp1 = fullCond;
	// 				tmp2 = unchanged;
	// 				unchanged = tmp1.and(tmp2);
	// 				tmp1.free();
	// 				tmp2.free();*/
	// 			/*}
    //             cond.free();
    //             tmp1 = action;
    //             action = tmp1.and(fullCond);
    //             tmp1.free();
    //             fullCond.free();*/
                


    //             /*for (int i = 0; i < numberOfVars; i++) {
    //                 tmp1 = variables[(currentVariable + i) * 2];
    //                 tmp1 = tmp1.biimp(variables[(currentVariable + i) * 2 + 1]);
    //                 tmp2 = cond;
    //                 cond = tmp1.and(tmp2);
    //                 tmp1.free();
    //                 tmp2.free();
    //             }
    //             System.out.print("non-ceff: ");
    //             cond.printSet();
    //             tmp1 = action;
    //             action = tmp1.or(cond);
    //             System.out.print("action after non-ceff: ");
    //             action.printSet();
    //             tmp1.free();
    //             cond.free();*/


    //             /*tmp1 = cond;
    //             cond = cond.biimp(unchanged);
    //             tmp1.free();
    //             unchanged.free();
    //             tmp1 = action;
    //             action = tmp1.and(cond);
    //             tmp1.free();
    //             cond.free();*/
    //         } else if (!oneVariableInserted) {
	// 			for (int i = 0; i < numberOfVars; i++) {
	// 				tmp1 = variables[(currentVariable + i) * 2];
	// 				tmp1 = tmp1.biimp(variables[(currentVariable + i) * 2 + 1]);
    //                 System.out.print("eq: ");
    //                 tmp1.printSet();
	// 				tmp2 = action;
	// 				action = tmp1.and(tmp2);
    //                 System.out.print("action after eq: ");
    //                 action.printSet();
	// 				tmp1.free();
	// 				tmp2.free();
	// 			}
	// 		} else if (!positiveVariableInserted) {
	// 			if (group.getLast().startsWith("none-of-these")) {
	// 				tmp1 = action;
	// 				action = tmp1.and(nAryVariablesEffBDDs.get(nAryVariables
	// 						.indexOf(group.getLast())));
	// 				tmp1.free();
	// 			} else {
	// 				System.err
	// 						.println("Error: only negated variable of group "
	// 								+ partitionCounter
	// 								+ " in effect though there is no \'none-of-these\'-variable!");
	// 				System.exit(1);
	// 			}
	// 		}
	// 		partitionCounter++;
	// 		currentVariable += numberOfVars;
	// 	}
    //     /*System.out.println("action: " + name);
    //       action.printSet();*/
    //     action.printSet();
    //     System.out.println("sat: " + (long) action.satCount());
    //     //System.exit(1);
	// 	return action;
	// }

        BDD effBDD = createEffBDD(preBDD, factory, nAryVariables, nAryVariablesPreBDDs, nAryVariablesEffBDDs, partitionedVariables, variables, unusedVarIndices);
        if (effBDD == null) {
            preBDD.free();
            return null;
        }
        BDD action = preBDD.and(effBDD);
        preBDD.free();
        effBDD.free();
        //System.out.println("action BDD (size: " + (long) action.satCount() + "): ");
        //action.printSet();
        return action;
    }

    private BDD createEffBDD(BDD preBDD, BDDFactory factory, LinkedList<String> nAryVariables,
			LinkedList<BDD> nAryVariablesPreBDDs,
			LinkedList<BDD> nAryVariablesEffBDDs,
			LinkedList<LinkedList<String>> partitionedVariables,
			BDD[] variables, boolean[] unusedVarIndices) {
        BDD tmp1;
        BDD tmp2;
        BDD tmp3;
	 	BDD effBDD = effect.createBDD(factory, nAryVariables, nAryVariablesPreBDDs, nAryVariablesEffBDDs, false, unusedVarIndices);
        if (effBDD == null) {
            // no normal effects (with the set of unabstracted variables)
            effBDD = factory.one();
        }

		HashSet<String> addEffects = new HashSet<String>();
		HashSet<String> delEffects = new HashSet<String>();
        Vector<Condition> condEffects = new Vector<Condition>();
        Vector<HashSet<String>> condEffectVars = new Vector<HashSet<String>>();
		effect.classifyEffects(addEffects, delEffects, condEffects, condEffectVars, false, false);

        ListIterator<LinkedList<String>> partitionIt = partitionedVariables.listIterator();
        int partID = 0;
        int currentVariable = 0; // log representation
        int currentBinaryVariable = 0; // one-shot representation
        while (partitionIt.hasNext()) {
            LinkedList<String> group = partitionIt.next();
            int size = group.size();
            int numberOfVars = Maths.log2(size);

            // check for presence in conditional effects
            ListIterator<HashSet<String>> condIt = condEffectVars.listIterator();
            int condID = 0;
            boolean inConditionalEffect = false;
            Vector<Integer> condIDs = new Vector<Integer>();
            while (condIt.hasNext()) {
                HashSet<String> condVars = condIt.next();
                ListIterator<String> varIt = group.listIterator();
                while (varIt.hasNext()) {
                    String var = varIt.next();
                    if (condVars.contains(var)) {
                        inConditionalEffect = true;
                        condIDs.add(condID);
                        break;
                    }
                }
                condID++;
            }
            //System.out.println("group ID: " + partID);
            if (inConditionalEffect) {
                // if at least one condition fires: set changed value
                BDD varBDD = factory.zero();
                boolean[] unusedEffVarIndices = new boolean[unusedVarIndices.length];
                for (int i = 0; i < currentVariable; i++) {
                    unusedEffVarIndices[i] = true;
                }
                for (int i = currentVariable; i < currentBinaryVariable + size; i++) {
                    unusedEffVarIndices[i] = unusedVarIndices[i];
                }
                for (int i = currentBinaryVariable + size; i < unusedVarIndices.length; i++) {
                    unusedEffVarIndices[i] = true;
                }
                /*for (int i = 0; i < unusedEffVarIndices.length; i++) {
                    if (unusedEffVarIndices[i])
                        System.out.print(" 1");
                    else
                        System.out.print(" 0");
                }
                System.out.println();*/
                for (int i = 0; i < condIDs.size(); i++) {
                    /*
                    BDD condBDD = factory.one();
                    for (int j = 0; j < condIDs.size(); j++) {
                        Condition cond = condEffects.get(condIDs.get(j));
                        tmp1 = cond.createPreBDD(factory, nAryVariables, nAryVariablesPreBDDs, unusedVarIndices);
                        if (i != j) {
                            tmp2 = tmp1.not();
                            tmp1.free();
                            tmp1 = cond.createEffBDD(factory, nAryVariables, nAryVariablesEffBDDs, unusedVarIndices, i);
                            tmp3 = tmp1.and(tmp2);
                            tmp1.free();
                            tmp2.free();
                            tmp1 = tmp3;
                        }
                        tmp2 = condBDD;
                        condBDD = tmp1.and(tmp2);
                        tmp1.free();
                        tmp2.free();
                    }
                    tmp1 = varBDD;
                    varBDD = tmp1.or(condBDD);
                    tmp1.free();
                    condBDD.free();
                    */
                    Condition cond = condEffects.get(condIDs.get(i));
                    tmp1 = cond.createPreBDD(factory, nAryVariables, nAryVariablesPreBDDs, unusedVarIndices);
                    tmp2 = cond.createEffBDD(factory, nAryVariables, nAryVariablesEffBDDs, unusedEffVarIndices);
                    tmp3 = tmp1.and(tmp2);
                    tmp1.free();
                    tmp2.free();
                    tmp1 = varBDD;
                    varBDD = tmp1.or(tmp3);
                    tmp1.free();
                    tmp3.free();
                }

                // if no condition fires: retain old value
                BDD negCondBDD = factory.one();
                for (int i = 0; i < condIDs.size(); i++) {
                    Condition cond = condEffects.get(condIDs.get(i));
                    tmp1 = cond.createPreBDD(factory, nAryVariables, nAryVariablesPreBDDs, unusedVarIndices);
                    tmp2 = tmp1.not();
                    tmp1.free();
                    tmp1 = negCondBDD;
                    negCondBDD = tmp1.and(tmp2);
                    tmp1.free();
                    tmp2.free();
                }
                for (int i = 0; i < numberOfVars; i++) {
                    tmp1 = variables[(currentVariable + i) * 2];
					tmp1 = tmp1.biimp(variables[(currentVariable + i) * 2 + 1]);
					tmp2 = negCondBDD;
					negCondBDD = tmp1.and(tmp2);
					tmp1.free();
					tmp2.free();
				}
                tmp1 = varBDD;
                varBDD = tmp1.or(negCondBDD);
                tmp1.free();
                negCondBDD.free();

                // add to effect BDD
                tmp1 = effBDD;
                effBDD = tmp1.and(varBDD);
                tmp1.free();
                varBDD.free();
            }

            // check for presence in normal effects
            ListIterator<String> varIt = group.listIterator();
            boolean oneVariableInserted = false;
            boolean positiveVariableInserted = false;
            while (varIt.hasNext()) {
                String var = varIt.next();
				if (addEffects.contains(var)) {
					oneVariableInserted = true;
					positiveVariableInserted = true;
                    // cannot be a positive effect and in some conditional effect
                    // thus, safe to break here
					break;
				}
				if (!oneVariableInserted && delEffects.contains(var))
					oneVariableInserted = true;
            }
            if (oneVariableInserted && inConditionalEffect) {
                    System.err.println("Error: negated variable outside conditional effects, but same variable also inside conditional effects!");
                    System.exit(1);
            }                
            //System.out.println("var " + partID + ": inCond: " + inConditionalEffect + "; pos: " + positiveVariableInserted + "; varIn: " + oneVariableInserted);
            if (!oneVariableInserted && !inConditionalEffect) {
				for (int i = 0; i < numberOfVars; i++) {
					tmp1 = variables[(currentVariable + i) * 2];
					tmp1 = tmp1.biimp(variables[(currentVariable + i) * 2 + 1]);
					tmp2 = effBDD;
					effBDD = tmp1.and(tmp2);
					tmp1.free();
					tmp2.free();
				}
			} else if (!positiveVariableInserted) {
                if (!inConditionalEffect) {
                    if (group.getLast().startsWith("none-of-these")) {
                        tmp1 = effBDD;
                        effBDD = tmp1.and(nAryVariablesEffBDDs.get(nAryVariables
                                                                   .indexOf(group.getLast())));
                        tmp1.free();
                    } else {
                        System.err
							.println("Error: only negated variable of group "
                                     + partID
                                     + " in effect though there is no \'none-of-these\'-variable!");
                        System.exit(1);
                    }
                }
			}

            partID++;
            currentVariable += numberOfVars;
            currentBinaryVariable += size;
        }
        return effBDD;
    }

	public void setName(String name) {
		this.name = name;
	}

	public String getName() {
		return name;
	}

	public void setCost(int cost) {
		this.cost = cost;
	}

	public int getCost() {
		return cost;
	}

	public void setPrecondition(Expression precondition) {
		this.precondition = precondition;
	}

	public Expression getPrecondition() {
		return precondition;
	}

	public void setEffect(Expression effect) {
		this.effect = effect;
		HashSet<String> delEffects = new HashSet<String>();
		HashSet<String> addEffects = new HashSet<String>();
		this.effect.findDelAdds(delEffects, addEffects, true);
		Iterator<String> delIt = delEffects.iterator();
		HashSet<String> delEffectsToEliminate = new HashSet<String>();
		while (delIt.hasNext()) {
			String predName = delIt.next();
			if (addEffects.contains(predName)) {
				delEffectsToEliminate.add(predName);
			}
		}
		if (delEffectsToEliminate.size() > 0) {
			effect.eliminateDelEffects(delEffectsToEliminate, true);
		}
	}

	public Expression getEffect() {
		return effect;
	}

	public boolean checkEffect(LinkedList<LinkedList<String>> partition) {
		boolean errorFound = false;
		HashSet<String> delEffects = new HashSet<String>();
		HashSet<String> addEffects = new HashSet<String>();
		effect.findDelAdds(delEffects, addEffects, true);
		ListIterator<LinkedList<String>> allPartitionIt = partition.listIterator();
		int partCounter = 0;
		while (allPartitionIt.hasNext()) {
			LinkedList<String> singlePartition = allPartitionIt.next();
			ListIterator<String> partitionIt = singlePartition.listIterator();
			boolean oneVariableInserted = false;
			boolean positiveVariableInserted = false;
			while (partitionIt.hasNext()) {
				String var = partitionIt.next();
				if (addEffects.contains(var)) {
					oneVariableInserted = true;
					positiveVariableInserted = true;
					break;
				}
				if (!oneVariableInserted && delEffects.contains(var))
					oneVariableInserted = true;
			}
			if (oneVariableInserted && !positiveVariableInserted) {
				if (!singlePartition.getLast().startsWith("none-of-these")) {
					errorFound = true;
					System.out.println("Warning: only negated variable of group " + partCounter + " in effect though there is no \'none-of-these\'-variable!");
					System.out.println("adding \'none-of-these\'-variable to group " + partCounter);
					singlePartition.addLast("none-of-these-" + partCounter);
				}
			}
			partCounter++;
		}
		return errorFound;
	}

	public void setUnused(boolean unused) {
		this.unused = unused;
	}

	public boolean getUnused() {
		return unused;
	}

	public Vector<Predicate> getAllPredicates() {
		Vector<Predicate> allPreds = new Vector<Predicate>();
		precondition.getAllPredicates(allPreds);
		effect.getAllPredicates(allPreds);
		return allPreds;
	}

	public void createSyntaxTree(SyntaxTreeNode root, SyntaxTree tree,
			LinkedList<LinkedList<String>> partitions) {
		SyntaxTreeNode actionNode = new SyntaxTreeNode();
		root.addSuccessor(actionNode);
		precondition.createSyntaxTree(actionNode, tree, partitions);
		effect.createSyntaxTree(actionNode, tree, partitions);
	}

	public String toString() {
		String ret = "action " + name + ":\n";
		ret += "cost: " + cost + "\n";
		ret += "precondition:\n";
		ret += precondition.toString() + "\n";
		ret += "effect:\n";
		ret += effect.toString() + "\n\n";
		return ret;
	}

	private String name;
	private int cost;
	private Expression precondition;
	private Expression effect;
	private boolean unused;
}
