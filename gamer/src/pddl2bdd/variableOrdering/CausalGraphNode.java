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

package pddl2bdd.variableOrdering;

import java.util.*;

/**
 *
 * @author Peter Kissmann
 * @version 1.9
 */
public class CausalGraphNode implements Comparable<CausalGraphNode> {
    private int variable;
    private LinkedList<CausalGraphNode> successors;
    private LinkedList<CausalGraphNode> predecessors;

    public CausalGraphNode(int variable) {
        this.variable = variable;
        successors = new LinkedList<CausalGraphNode>();
        predecessors = new LinkedList<CausalGraphNode>();
    }

    public void addSuccessor(CausalGraphNode succ, boolean removeDuplicates) {
    	if (removeDuplicates) {
	        if (succ != this && !successors.contains(succ)) {
	            successors.add(succ);
	            succ.addPredecessor(this);
	        }
    	} else {
    		if (succ != this) {
    			successors.add(succ);
    			succ.addPredecessor(this);
    		}
    	}
    }

    public int getNumberOfSuccessors() {
        return successors.size();
    }

    public CausalGraphNode getSuccessor(int index) {
        return successors.get(index);
    }

    public void addPredecessor(CausalGraphNode pre) {
        if (pre != this && !predecessors.contains(pre)) {
            predecessors.add(pre);
        }
    }

    public boolean hasPredecessors() {
        return !predecessors.isEmpty();
    }

    public void removeFromSuccessors() {
        ListIterator<CausalGraphNode> succIt = successors.listIterator();
        while (succIt.hasNext()) {
            CausalGraphNode succ = succIt.next();
            succ.removePredecessor(this);
        }
    }

    public void removeFromSuccessors(LinkedList<Integer> unusedVariables, LinkedList<Integer> nextVariables) {
        ListIterator<CausalGraphNode> succIt = successors.listIterator();
        while (succIt.hasNext()) {
            CausalGraphNode succ = succIt.next();
            succ.removePredecessor(this);
            int var = succ.getVariable();
            if (unusedVariables.contains(var) && !nextVariables.contains(var))
                nextVariables.add(var);
        }
    }

    public void removePredecessor(CausalGraphNode node) {
        ListIterator<CausalGraphNode> preIt = predecessors.listIterator();
        while (preIt.hasNext()) {
            CausalGraphNode preNode = preIt.next();
            if (preNode == node) {
                preIt.remove();
                break;
            }
        }
    }

    public int getVariable() {
        return variable;
    }

    public int compareTo(CausalGraphNode other) {
        if (variable < other.getVariable())
            return -1;
        else if (variable == other.getVariable())
            return 0;
        else
            return 1;
    }

    public void sort() {
        Collections.sort(successors);
        Collections.sort(predecessors);
    }

    public String toString() {
        String out = "   ";
        out += variable + ":";
        ListIterator<CausalGraphNode> succIt = successors.listIterator();
        while (succIt.hasNext()) {
            out += " " + succIt.next().getVariable();
        }
        out += "\n";
        out += "      (successor of";
        succIt = predecessors.listIterator();
        while (succIt.hasNext()) {
            out += " " + succIt.next().getVariable();
        }
        out += ")";
        return out;
    }
}
