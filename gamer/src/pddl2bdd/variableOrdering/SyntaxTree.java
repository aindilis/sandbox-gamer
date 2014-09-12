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

import pddl2bdd.parser.GroundedPDDLParser;
import pddl2bdd.parser.logic.*;
import java.util.*;

/**
 *
 * @author Peter Kissmann
 * @version 1.9
 */
public class SyntaxTree {
    private SyntaxTreeNode root;
    private LinkedList<SyntaxTreeLeaf> leaves;

    public SyntaxTree(LinkedList<LinkedList<String>> partitions) {
        root = new SyntaxTreeNode();
        leaves = new LinkedList<SyntaxTreeLeaf>();

        ListIterator<Action> actionIt = GroundedPDDLParser.actions.listIterator();
        while (actionIt.hasNext()) {
            Action ac = actionIt.next();
            ac.createSyntaxTree(root, this, partitions);
        }
    }

    public void setBFSValues() {
        root.setBFSValues(0);
    }

    public void setInverseBFSValues() {
        ListIterator<SyntaxTreeLeaf> leavesIt = leaves.listIterator();
        while (leavesIt.hasNext()) {
            leavesIt.next().setInverseBFSValues(0);
        }
    }

    // type: 0 = based on values (max first); 1 = based on #vars (max first)
    public int[] performDFS(int type, Random rnd) {
        int[] variablesDFSOrder = new int[leaves.size()];
        root.performDFS(type, 0, variablesDFSOrder, rnd);
        return variablesDFSOrder;
    }

    public void assignWeights() {
        root.assignWeights(1.0);
    }

    public double[] getVariableWeights(int size) {
        double[] variableWeights = new double[size];
        ListIterator<SyntaxTreeLeaf> leavesIt = leaves.listIterator();
        while (leavesIt.hasNext()) {
            SyntaxTreeLeaf leaf = leavesIt.next();
            variableWeights[leaf.getVariable()] += leaf.getWeight();
        }
        return variableWeights;
    }

    public void removeLeaves(int variable) {
        ListIterator<SyntaxTreeLeaf> leavesIt = leaves.listIterator();
        while (leavesIt.hasNext()) {
            SyntaxTreeLeaf leaf = leavesIt.next();
            if (leaf.getVariable() == variable) {
                leaf.removeNode();
                leavesIt.remove();
            }
        }
    }

    public void calculateShortestDistances(int[][] distances) {
    	for (int i = 0; i < distances.length; i++) {
    		ListIterator<SyntaxTreeLeaf> leavesIt = leaves.listIterator();
    		while (leavesIt.hasNext()) {
    			leavesIt.next().determineDistances(-1, 0, distances);
    		}
    	}
    	/*for (int i = 0; i < distances.length - 1; i++) {
    		System.out.println("BFS for var " + i);
    		LinkedList<SyntaxTreeNode> open = new LinkedList<SyntaxTreeNode>();
    		ListIterator<SyntaxTreeLeaf> leavesIt = leaves.listIterator();
    		while (leavesIt.hasNext()) {
    			SyntaxTreeLeaf leaf = leavesIt.next();
    			if (leaf.getVariable() == i)
    				open.add(leaf);
    		}
        	LinkedList<SyntaxTreeNode> closed = new LinkedList<SyntaxTreeNode>();
        	LinkedList<Integer> unfoundIndices = new LinkedList<Integer>();
        	for (int j = i + 1; j < distances.length; j++) {
        		unfoundIndices.add(j);
        	}
    		bfs(open, closed, unfoundIndices, 0, i, distances);
    	}*/
    }

    /*public void bfs(LinkedList<SyntaxTreeNode> open, LinkedList<SyntaxTreeNode> closed, LinkedList<Integer> unfoundIndices, int depth, int current, int[][] distances) {
    	if (open.isEmpty()) {
    		System.err.println("Error: Open List empty!");
    		Exception e = new Exception();
    		e.printStackTrace();
    	}
    	LinkedList<SyntaxTreeNode> newOpen = new LinkedList<SyntaxTreeNode>();
    	ListIterator<SyntaxTreeNode> openIt = open.listIterator();
    	while (openIt.hasNext()) {
    		SyntaxTreeNode openNode = openIt.next();
    		SyntaxTreeNode succ = openNode.getParent();
    		if (succ != null && !open.contains(succ) && !closed.contains(succ))
    			newOpen.add(succ);
    		LinkedList<Integer> vars = openNode.getVariables(); 
    		ListIterator<Integer> varsIt = vars.listIterator();
    		boolean allFound = true;
    		while (varsIt.hasNext()) {
    			if (unfoundIndices.contains(varsIt.next())) {
    				allFound = false;
    				break;
    			}
    		}
    		if (allFound)
    			continue;
    		for (int i = 0; i < openNode.getNumberOfSuccessors(); i++) {
    			succ = openNode.getSuccessor(i);
    			if (succ instanceof SyntaxTreeLeaf) {
    				SyntaxTreeLeaf leaf = (SyntaxTreeLeaf) succ;
    				int var = leaf.getVariable();
    				if (unfoundIndices.contains(var)) {
    					System.out.println("reached " + var);
    					distances[current][var] = depth + 1;
    					distances[var][current] = depth + 1;
    					unfoundIndices.removeFirstOccurrence(var);
    					if (unfoundIndices.isEmpty())
    						return;
    				}
    			}
    			if (!open.contains(succ) && !closed.contains(succ))
    				newOpen.add(succ);
    		}
    		closed.add(openNode);
    	}
    	open.clear();
    	bfs(newOpen, closed, unfoundIndices, depth + 1, current, distances);
    }*/

    public int shortestDistance(int var1, int var2) {
        int distance = Integer.MAX_VALUE;
        ListIterator<SyntaxTreeLeaf> leavesIt1 = leaves.listIterator();
        while (leavesIt1.hasNext()) {
            SyntaxTreeLeaf leaf = leavesIt1.next();
            if (leaf.getVariable() != var1)
                continue;
            LinkedList<SyntaxTreeNode> path1 = leaf.getPath();
            ListIterator<SyntaxTreeLeaf> leavesIt2 = leaves.listIterator();
            while (leavesIt2.hasNext()) {
                leaf = leavesIt2.next();
                if (leaf.getVariable() != var2)
                    continue;
                LinkedList<SyntaxTreeNode> path2 = leaf.getPath();
                ListIterator<SyntaxTreeNode> path2It = path2.listIterator();
                int index2 = 0;
                while (path2It.hasNext()) {
                    SyntaxTreeNode node = path2It.next();
                    if (path1.contains(node)) {
                        int index1 = path1.indexOf(node);
                        if (index1 + index2 < distance)
                            distance = index1 + index2;
                        break;
                    }
                    index2++;
                }
            }
        }
        return distance;
    }

    public void addLeaf(SyntaxTreeLeaf leaf) {
        leaves.add(leaf);
    }

    public LinkedList<SyntaxTreeLeaf> getLeaves() {
        return leaves;
    }

    public String toString() {
        String out = "";
        out += root.toString(0);
        out += "all leaves:\n";
        for (int i = 0; i < leaves.size(); i++) {
            out += leaves.get(i) + "\n";
        }
        out += "\nall variables:\n";
        for (int i = 0; i < root.getVariables().size(); i++) {
            out += root.getVariables().get(i) + " ";
        }
        out += "\n";
        return out;
    }
}
