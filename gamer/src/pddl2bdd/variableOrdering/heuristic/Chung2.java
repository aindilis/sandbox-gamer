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
public class Chung2 extends VariableOrderingHeuristic {
    public int[] findVariableOrdering(LinkedList<LinkedList<String>> partitions) {
        SyntaxTree tree = new SyntaxTree(partitions);
        //System.out.println(tree);
        /*int[][] distances = new int[partitions.size()][partitions.size()];
        for (int i = 0; i < distances.length; i++) {
            distances[i][i] = Integer.MAX_VALUE;
        }
        for (int i = 0; i < distances.length - 1; i++) {
            for (int j = i + 1; j < distances.length; j++) {
            	System.out.println("calculating distance for " + i + " and " + j);
                distances[i][j] = distances[j][i] = tree.shortestDistance(i, j);
            }
        }*/
        int[][] distances = new int[partitions.size()][partitions.size()];
        for (int i = 0; i < distances.length; i++) {
        	for (int j = 0; j < distances.length; j++) {
        		if (i == j)
        			distances[i][j] = 0;
        		else
        			distances[i][j] = Integer.MAX_VALUE;
        	}
        }
        tree.calculateShortestDistances(distances);
        /*for (int i = 0; i < distances.length; i++) {
            for (int j = 0; j < distances.length; j++) {
                System.out.print(distances[i][j] + " ");
            }
            System.out.println();
        }*/
        int[] totalDistances = new int[distances.length];
        for (int i = 0; i < distances.length; i++) {
            for (int j = 0; j < distances.length; j++) {
                if (i != j)
                    totalDistances[i] += distances[i][j];
            }
        }
        /*System.out.println();
        for (int i = 0; i < totalDistances.length; i++) {
            System.out.println(i + ": " + totalDistances[i]);
        }*/
        LinkedList<Integer> smallestTotalIndices = new LinkedList<Integer>();
        int smallestTotal = Integer.MAX_VALUE;
        for (int i = 0; i < totalDistances.length; i++) {
            if (totalDistances[i] < smallestTotal) {
                smallestTotal = totalDistances[i];
                smallestTotalIndices.clear();
                smallestTotalIndices.add(i);
            } else if (totalDistances[i] == smallestTotal) {
                smallestTotalIndices.add(i);
            }
        }
        //System.out.println(smallestTotalIndices);
        LinkedList<Integer> usedVariables = new LinkedList<Integer>();
        int[] variableOrdering = new int[partitions.size()];
        variableOrdering[0] = smallestTotalIndices.get(rnd.nextInt(smallestTotalIndices.size()));
        usedVariables.add(variableOrdering[0]);

        for (int currentIndex = 1; currentIndex < variableOrdering.length; currentIndex++) {
            LinkedList<Integer> possibleNextVariables = new LinkedList<Integer>();
            int[] distancesToPrevious = new int[currentIndex];
            for (int i = 0; i < currentIndex; i++) {
                distancesToPrevious[i] = Integer.MAX_VALUE;
            }
            for (int i = 0; i < distances.length; i++) {
                if (usedVariables.contains(i))
                    continue;
                boolean isPossibleNext = true;
                for (int j = currentIndex - 1; j >= 0; j--) {
                    if (distances[i][variableOrdering[j]] > distancesToPrevious[j]) {
                        isPossibleNext = false;
                        break;
                    } else if (distances[i][variableOrdering[j]] < distancesToPrevious[j]) {
                        for (int k = j; k >= 0; k--) {
                            distancesToPrevious[k] = distances[i][variableOrdering[k]];
                        }
                        possibleNextVariables.clear();
                    }
                }
                if (isPossibleNext) {
                    possibleNextVariables.add(i);
                }
            }
            //System.out.println("possible next vars: " + possibleNextVariables);
            variableOrdering[currentIndex] = possibleNextVariables.get(rnd.nextInt(possibleNextVariables.size()));
            usedVariables.add(variableOrdering[currentIndex]);
        }

        for (int i = 0; i < variableOrdering.length; i++) {
            System.out.print(variableOrdering[i] + " ");
        }
        System.out.println();
        return variableOrdering;
    }
}
