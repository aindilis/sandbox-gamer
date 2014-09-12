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
public class Malik extends VariableOrderingHeuristic {
    public int[] findVariableOrdering(LinkedList<LinkedList<String>> partitions) {
        SyntaxTree tree = new SyntaxTree(partitions);
        tree.setBFSValues();
        int[] minValues = new int[partitions.size()];
        for (int i = 0; i < minValues.length; i++) {
            minValues[i] = Integer.MAX_VALUE;
        }
        LinkedList<SyntaxTreeLeaf> leaves = tree.getLeaves();
        ListIterator<SyntaxTreeLeaf> leavesIt = leaves.listIterator();
        while (leavesIt.hasNext()) {
            SyntaxTreeLeaf leaf = leavesIt.next();
            int index = leaf.getVariable();
            if (leaf.getValue() < minValues[index])
                minValues[index] = leaf.getValue();
        }

        int[] variableOrdering = new int[partitions.size()];
        int counter = 0;
        int[] minIndices = new int[partitions.size()];
        while (counter < partitions.size()) {
            int minValue = Integer.MAX_VALUE;
            int internalCounter = 0;
            for (int i = 0; i < minValues.length; i++) {
                if (minValues[i] < minValue) {
                    internalCounter = 1;
                    minIndices[0] = i;
                    minValue = minValues[i];
                } else if (minValues[i] == minValue) {
                    minIndices[internalCounter] = i;
                    internalCounter++;
                }
            }

            while (internalCounter > 0) {
                int rndNumber = rnd.nextInt(internalCounter);
                int index = minIndices[rndNumber];
                variableOrdering[counter] = index;
                minValues[index] = Integer.MAX_VALUE;
                counter++;
                internalCounter--;
                minIndices[rndNumber] = minIndices[internalCounter];
            }
        }

        for (int i = 0; i < variableOrdering.length; i++) {
            System.out.print(variableOrdering[i] + " ");
        }
        System.out.println();
        return variableOrdering;
    }
}
