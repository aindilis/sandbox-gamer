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
public class SyntaxTreeLeaf extends SyntaxTreeNode {
    private int variable;

    public SyntaxTreeLeaf(int variable) {
        super();
        this.variable = variable;
    }

    public void setBFSValues(int value) {
        this.value = value;
    }

    public void setInverseBFSValues(int value) {
        this.value = value;
        parent.setInverseBFSValues(value + 1);
    }

    public int performDFS(int type, int counter, int[] variablesDFSOrder, Random rnd) {
        variablesDFSOrder[counter] = variable;
        return counter + 1;
    }

    public void determineDistances(int var, int dist, int[][] minDistances) {
    	if (parent != null) {
    		parent.determineDistances(variable, dist + 1, minDistances);
    	}
    }

    public void assignWeights(double weight) {
        this.weight = weight;
    }

    public void removeNode() {
        parent.removeNode(this);
    }

    public int getVariable() {
        return variable;
    }

    public String toString(int indentation) {
        String out = "";
        for (int i = 0; i < indentation; i++)
            out += "  ";
        out += "l: " + variable + "; value: " + value + "; weight: " + weight + "\n";
        return out;
    }

    public String toString() {
        String out = "";
        out += variable;
        return out;
    }
}
