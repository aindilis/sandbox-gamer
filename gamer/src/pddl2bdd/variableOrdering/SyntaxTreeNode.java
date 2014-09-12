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
public class SyntaxTreeNode {
    protected LinkedList<SyntaxTreeNode> successors;
    protected SyntaxTreeNode parent;
    protected int value;
    protected double weight;
    protected LinkedList<Integer> variables;

    protected int[] distances;

    public SyntaxTreeNode() {
        successors = new LinkedList<SyntaxTreeNode>();
        variables = new LinkedList<Integer>();
        value = -1;
        weight = -1.0;
    }

    public void setBFSValues(int value) {
        this.value = value;
        ListIterator<SyntaxTreeNode> succIt = successors.listIterator();
        while (succIt.hasNext()) {
            succIt.next().setBFSValues(value + 1);
        }
    }

    public void setInverseBFSValues(int value) {
        if (value > this.value) {
            this.value = value;
            if (parent != null) {
                parent.setInverseBFSValues(value + 1);
            }
        }
    }

    // type: 0 = based on values (max first); 1 = based on #vars (max first)
    public int performDFS(int type, int counter, int[] variablesDFSOrder, Random rnd) {
        LinkedList<Integer> seenSuccessors = new LinkedList<Integer>();
        int[] maxIndices = new int[successors.size()];
        int maxValue = -1;
        int internalCounter = 0;
        int index = 0;
        while (seenSuccessors.size() != successors.size()) {
            index = 0;
            maxValue = -1;
            internalCounter = 0;
            ListIterator<SyntaxTreeNode> succIt = successors.listIterator();
            while (succIt.hasNext()) {
                SyntaxTreeNode successor = succIt.next();
                if (!seenSuccessors.contains(index)) {
                    int val = -1;
                    switch (type) {
                        case 0: {
                            val = successor.getValue();
                            break;
                        }
                        case 1: {
                            val = successor.getNumberOfVariables();
                        }
                    }
                    if (val > maxValue) {
                        internalCounter = 1;
                        maxIndices[0] = index;
                        maxValue = val;
                    } else if (val == maxValue) {
                        maxIndices[internalCounter] = index;
                        internalCounter++;
                    }
                }
                index++;
            }

            while (internalCounter > 0) {
                int rndNumber = rnd.nextInt(internalCounter);
                index = maxIndices[rndNumber];
                counter = successors.get(index).performDFS(type, counter, variablesDFSOrder, rnd);
                seenSuccessors.add(index);
                internalCounter--;
                maxIndices[rndNumber] = maxIndices[internalCounter];
            }
        }
        return counter;
    }

    public void determineDistances(int var, int dist, int[][] minDistances) {
    	if (distances == null) {
    		distances = new int[minDistances.length];
    		for (int i = 0; i < distances.length; i++) {
    			distances[i] = Integer.MAX_VALUE;
    		}
    		distances[var] = dist;
    	} else if (dist < distances[var]) {
    		distances[var] = dist;
    		for (int i = 0; i < distances.length; i++) {
    			if (i != var && distances[i] != Integer.MAX_VALUE && distances[i] + dist < minDistances[i][var]) {
    				minDistances[i][var] = distances[i] + dist;
    				minDistances[var][i] = distances[i] + dist;
    			}
    		}
    	}
    	if (parent != null) {
    		parent.determineDistances(var, dist + 1, minDistances);
    	}
    }

    public void assignWeights(double weight) {
        this.weight = weight;
        double succWeight = weight / successors.size();
        ListIterator<SyntaxTreeNode> succIt = successors.listIterator();
        while (succIt.hasNext()) {
            succIt.next().assignWeights(succWeight);
        }
    }

    public void removeNode(SyntaxTreeNode node) {
        ListIterator<SyntaxTreeNode> succIt = successors.listIterator();
        while (succIt.hasNext()) {
            SyntaxTreeNode successor = succIt.next();
            if (successor.equals(node)) {
                succIt.remove();
                break;
            }
        }
        if (successors.size() == 0 && parent != null) {
            parent.removeNode(this);
        }
    }

    public LinkedList<SyntaxTreeNode> getPath() {
        LinkedList<SyntaxTreeNode> path;
        if (parent == null) {
            path = new LinkedList<SyntaxTreeNode>();
        } else {
            path = parent.getPath();
        }
        path.addFirst(this);
        return path;
    }

    public void addSuccessor(SyntaxTreeNode node) {
        successors.add(node);
        node.setParent(this);
    }

    public SyntaxTreeNode getSuccessor(int index) {
        return successors.get(index);
    }

    public int getNumberOfSuccessors() {
        return successors.size();
    }

    public void addVariable(int variable) {
        if (!variables.contains(variable))
            variables.add(variable);
        if (parent != null)
            parent.addVariable(variable);
    }

    public LinkedList<Integer> getVariables() {
        return variables;
    }

    public int getNumberOfVariables() {
        return variables.size();
    }

    public SyntaxTreeNode getParent() {
        return parent;
    }

    public void setParent(SyntaxTreeNode node) {
        parent = node;
    }

    public int getValue() {
        return value;
    }

    public void setValue(int value) {
        this.value = value;
    }

    public double getWeight() {
        return weight;
    }

    public void setWeight(double weight) {
        this.weight = weight;
    }

    public String toString(int indentation) {
        String out = "";
        for (int i = 0; i < indentation; i++)
            out += "  ";
        out += "int" + "; value: " + value + "; weight: " + weight + "\n";
        for (int i = 0; i < successors.size(); i++) {
            out += successors.get(i).toString(indentation + 1);
        }
        return out;
    }
}
