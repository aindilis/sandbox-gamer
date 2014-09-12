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
public class Minato extends VariableOrderingHeuristic {
    public int[] findVariableOrdering(LinkedList<LinkedList<String>> partitions) {
        SyntaxTree tree = new SyntaxTree(partitions);
        int[] variableOrdering = new int[partitions.size()];
        for (int index = 0; index < partitions.size(); index++) {
            tree.assignWeights(); // an update might be better...
            double[] variableWeights = tree.getVariableWeights(partitions.size());
            int[] maxIndices = new int[partitions.size()];
            int counter = 0;
            double maxWeight = -1.0;
            for (int i = 0; i < variableWeights.length; i++) {
                if (variableWeights[i] > maxWeight) {
                    maxWeight = variableWeights[i];
                    counter = 1;
                    maxIndices[0] = i;
                } else if (variableWeights[i] == maxWeight) {
                    maxIndices[counter] = i;
                    counter++;
                }
            }
            int chosenIndex = maxIndices[rnd.nextInt(counter)];
            variableOrdering[index] = chosenIndex;
            tree.removeLeaves(chosenIndex);
        }
        for (int i = 0; i < variableOrdering.length; i++) {
            System.out.print(variableOrdering[i] + " ");
        }
        System.out.println();
        return variableOrdering;
    }
}
