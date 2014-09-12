/*
 * Gamer, a tool for finding optimal plans
 * Copyright (C) 2007-2012 by Peter Kissmann
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

package pddl2bdd.variableOrdering.heuristic;

import pddl2bdd.variableOrdering.*;
import java.util.*;

/**
 *
 * @author Peter Kissmann
 * @version 1.9
 */
public class CG extends VariableOrderingHeuristic {
	private boolean useBFSBased;
	private boolean useSingleStart;

	public CG() {
		useBFSBased = false;
		useSingleStart = false;
	}

	public CG(boolean useBFSBased) {
		this.useBFSBased = useBFSBased;
		useSingleStart = false;
	}

	public CG(boolean useBFSBased, boolean useSingleStart) {
		this.useBFSBased = useBFSBased;
		this.useSingleStart = useSingleStart;
	}

    public int[] findVariableOrdering(LinkedList<LinkedList<String>> partitions) {
        CausalGraph cg = new CausalGraph(partitions, false, true);
        System.out.println(cg);

        LinkedList<Integer> unusedVariables = new LinkedList<Integer>();
        for (int i = 0; i < partitions.size(); i++) {
            unusedVariables.add(i);
        }
        LinkedList<Integer> usedVariables = new LinkedList<Integer>();
        LinkedList<Integer> nonParentVariables = new LinkedList<Integer>();
        if (useBFSBased && !useSingleStart) {
        	int[] newVars = new int[cg.getNumberOfVariables()];
        	LinkedList<Integer> availableIndices = new LinkedList<Integer>();
        	for (int i = 0; i < newVars.length; i++) {
        		newVars[i] = -1;
        		availableIndices.add(i);
        	}
        	for (int i = 0; i < newVars.length; i++) {
        		CausalGraphNode node = cg.getVariable(i);
        		if (!node.hasPredecessors()) {
        			int availableIndex = availableIndices.remove(rnd.nextInt(availableIndices.size()));
        			newVars[availableIndex] = node.getVariable();
        		}
        	}
        	for (int i = 0; i < newVars.length; i++) {
        		if (newVars[i] != -1) {
        			nonParentVariables.add(newVars[i]);
        			//System.out.println("initially without parent: " + newVars[i]);
        		}
        	}
        }
        int currentIndex = 0;
        int[] variableOrdering = new int[partitions.size()];
        while (!unusedVariables.isEmpty()) {
            int index;
            LinkedList<Integer> nextVariables = new LinkedList<Integer>();
        	if (!nonParentVariables.isEmpty()) { // only relevant in BFS-style tie-breaking
        		nextVariables.add(nonParentVariables.removeFirst());
        	} else {
	            ListIterator<Integer> unusedIt = unusedVariables.listIterator();
	            while (unusedIt.hasNext()) {
	                index = unusedIt.next();
	                if (!cg.getVariable(index).hasPredecessors())
	                    nextVariables.add(index);
	            }
	            if (nextVariables.isEmpty()) {
	                unusedIt = usedVariables.listIterator();
	                while (unusedIt.hasNext()) {
	                    index = unusedIt.next();
	                    CausalGraphNode var = cg.getVariable(index);
	                    for (int i = 0; i < var.getNumberOfSuccessors(); i++) {
	                    	int nextVar = var.getSuccessor(i).getVariable();
	                        if (!usedVariables.contains(nextVar))
	                            nextVariables.add(nextVar);
	                    }
	                }
	            }
	            if (nextVariables.isEmpty()) {
	                nextVariables.add(unusedVariables.remove(rnd.nextInt(unusedVariables.size())));
	            }
        	}
            //while (!nextVariables.isEmpty()) {
                //System.out.println(nextVariables);
                index = nextVariables.get(rnd.nextInt(nextVariables.size()));
                //System.out.println("chosen: " + index);
                unusedVariables.removeFirstOccurrence(index);
                usedVariables.add(index);
                cg.getVariable(index).removeFromSuccessors();
                if (useBFSBased) {
                	CausalGraphNode curr = cg.getVariable(index);
                	int succNum = curr.getNumberOfSuccessors();
                	int[] newVars = new int[succNum];
                	LinkedList<Integer> availableIndices = new LinkedList<Integer>();
                	for (int i = 0; i < succNum; i++) {
                		newVars[i] = -1;
                		availableIndices.add(i);
                	}
                	for (int i = 0; i < succNum; i++) {
                		CausalGraphNode succ = curr.getSuccessor(i);
                		if (!succ.hasPredecessors() && !usedVariables.contains(succ.getVariable())) {
                			int availableIndex = availableIndices.remove(rnd.nextInt(availableIndices.size()));
                			newVars[availableIndex] = succ.getVariable();
                		}
                	}
                	for (int i = 0; i < succNum; i++) {
                		if (newVars[i] != -1) {
                			nonParentVariables.add(newVars[i]);
                			//System.out.println("newly without parent: " + newVars[i]);
                		}
                	}
                }
                variableOrdering[currentIndex] = index;
                currentIndex++;
                //System.out.println("next: " + index);
            //}
        }
        for (int i = 0; i < variableOrdering.length; i++) {
            System.out.print(variableOrdering[i] + " ");
        }
        System.out.println();
        return variableOrdering;
    }
}
