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

import pddl2bdd.parser.GroundedPDDLParser;
import pddl2bdd.parser.logic.*;
import java.util.*;

/**
 *
 * @author Peter Kissmann
 * @version 1.9
 */
public class Greedy extends VariableOrderingHeuristic {
    public int[] findVariableOrdering(LinkedList<LinkedList<String>> partitions) {
        int[] variableOrdering = new int[partitions.size()];
        int weights[] = new int[partitions.size()];

        LinkedList<LinkedList<Integer>> allIndices = getActionsPredicateIndices(partitions);
        for (int i = 0; i < variableOrdering.length; i++) {
            for (int j = 0; j < weights.length; j++) {
                if (weights[j] == -1)
                    continue;
                variableOrdering[i] = j; // only temporarily for easier weight calculation
                weights[j] = calculateWeight(allIndices, variableOrdering, i + 1);
            }
            int val = 0;
            int index = -1;
            for (int j = 0; j < weights.length; j++) {
                if (weights[j] > val || (weights[j] == val && rnd.nextBoolean())) {
                    index = j;
                    val = weights[j];
                }
            }
            variableOrdering[i] = index;
            weights[index] = -1;
        }
        for (int i = 0; i < variableOrdering.length; i++) {
            System.out.print(variableOrdering[i] + " ");
        }
        System.out.println();
        return variableOrdering;
    }

    private int calculateWeight(LinkedList<LinkedList<Integer>> allIndices, int[] ordering, int orderingSize) {
        int counter = 0;
        for (int i = 0; i < orderingSize; i++) {
            ListIterator<LinkedList<Integer>> allIndicesIt = allIndices.listIterator();
            while (allIndicesIt.hasNext()) {
                if (allIndicesIt.next().contains(ordering[i]))
                    counter++;
            }
        }
        return counter;
    }

    private LinkedList<LinkedList<Integer>> getActionsPredicateIndices(LinkedList<LinkedList<String>> partitions) {
        LinkedList<LinkedList<Integer>> allIndices = new LinkedList<LinkedList<Integer>>();
        ListIterator<Action> actionIt = GroundedPDDLParser.actions.listIterator();
        while (actionIt.hasNext()) {
            Vector<Predicate> allPreds = actionIt.next().getAllPredicates();
            String name;
            LinkedList<Integer> foundIndices = new LinkedList<Integer>();
            for (int i = 0; i < allPreds.size(); i++) {
                name =  allPreds.get(i).getName();
                for (int j = 0; j < partitions.size(); j++) {
                    if (partitions.get(j).contains(name)) {
                        if (!foundIndices.contains(j)) {
                            foundIndices.add(j);
                        }
                        break;
                    }
                }
            }
            allIndices.add(foundIndices);
        }
        return allIndices;
    }
}
