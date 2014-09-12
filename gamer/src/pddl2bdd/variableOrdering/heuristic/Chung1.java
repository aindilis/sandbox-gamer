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
public class Chung1 extends VariableOrderingHeuristic {
    public int[] findVariableOrdering(LinkedList<LinkedList<String>> partitions) {
        SyntaxTree tree = new SyntaxTree(partitions);
        tree.setInverseBFSValues();
        int[] variablesDFSOrder = tree.performDFS(0, rnd);
        boolean[] usedVariables = new boolean[partitions.size()];
        int index = 0;
        int[] variableOrdering = new int[partitions.size()];
        for (int i = 0; i < variablesDFSOrder.length; i++) {
            int nextIndex = variablesDFSOrder[i];
            if (!usedVariables[nextIndex]) {
                variableOrdering[index] = nextIndex;
                usedVariables[nextIndex] = true;
                index++;
            }
        }
        for (int i = 0; i < variableOrdering.length; i++) {
            System.out.print(variableOrdering[i] + " ");
        }
        System.out.println();
        return variableOrdering;
    }
}
