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
public class Gamer extends VariableOrderingHeuristic {
	private boolean bidir;
	private boolean inverse;

	public Gamer(boolean bidir, boolean inverse) {
		this.bidir = bidir;
		this.inverse = inverse;
	}

	public Gamer(boolean bidir) {
		this.bidir = bidir;
		inverse = false;
	}

	public Gamer() {
		bidir = false;
		inverse = false;
	}

    public int[] findVariableOrdering(LinkedList<LinkedList<String>> partitions) {
    	CausalGraph cg = new CausalGraph(partitions, bidir, true);
    	boolean[][] influences = new boolean[partitions.size()][partitions.size()];
    	for (int i = 0; i < influences.length; i++) {
    		CausalGraphNode node = cg.getVariable(i);
    		CausalGraphNode succ;
    		for (int j = 0; j < node.getNumberOfSuccessors(); j++) {
    			succ = node.getSuccessor(j);
    			influences[i][succ.getVariable()] = true;
    			influences[succ.getVariable()][i] = true;
    		}
    	}

        int[] variableOrdering = new int[influences.length];
        for (int i = 0; i < variableOrdering.length; i++) {
            variableOrdering[i] = i;
        }
        int[] bestVariableOrdering = new int[influences.length];
        long bestTotalDistance = Integer.MAX_VALUE;
        for (int i = 0; i < 20; i++) {
            long totalDistance;
            totalDistance = findOneVariableOrdering(influences,
                    variableOrdering, rnd);
            if (totalDistance < bestTotalDistance) {
                bestTotalDistance = totalDistance;
                bestVariableOrdering = variableOrdering.clone();
            }
            System.out.println(bestTotalDistance);
        }
        System.out.println(bestTotalDistance);
        if (inverse) {
        	int[] tmpOrdering = new int[bestVariableOrdering.length];
        	for (int i = 0; i < tmpOrdering.length; i++) {
        		tmpOrdering[i] = bestVariableOrdering[i];
        	}
        	for (int i = 0; i < tmpOrdering.length; i++) {
        		bestVariableOrdering[bestVariableOrdering.length - i - 1] = tmpOrdering[i];
        	}
        }
        for (int i = 0; i < bestVariableOrdering.length; i++) {
            System.out.print(bestVariableOrdering[i] + " ");
        }
        System.out.println();
        return bestVariableOrdering;
    }

    private long findOneVariableOrdering(boolean[][] influences,
            int[] variableOrdering, Random rnd) {
        int swapIndex1 = 0;
        int swapIndex2 = 0;
        int tmpVariable;
        for (int i = variableOrdering.length - 1; i >= 1; i--) {
            tmpVariable = variableOrdering[i];
            swapIndex1 = rnd.nextInt(i + 1);
            variableOrdering[i] = variableOrdering[swapIndex1];
            variableOrdering[swapIndex1] = tmpVariable;
        }

        long oldTotalDistance = Integer.MAX_VALUE;
        long totalDistance = 0;
        for (int i = 0; i < variableOrdering.length - 1; i++) {
            for (int j = i + 1; j < variableOrdering.length; j++) {
                if (influences[variableOrdering[i]][variableOrdering[j]]
                        || influences[variableOrdering[j]][variableOrdering[i]]) {
                    totalDistance += Math.max(i - j, j - i)
                            * Math.max(i - j, j - i);
                }
            }
        }
        System.out.println("initial distance: " + totalDistance);
        oldTotalDistance = totalDistance;
        for (int counter = 0; counter < 50000; counter++) {
            swapIndex1 = rnd.nextInt(variableOrdering.length);
            swapIndex2 = rnd.nextInt(variableOrdering.length);
            // System.out.println(influences[variableOrdering[swapIndex1]][variableOrdering[swapIndex2]]);
            for (int i = 0; i < variableOrdering.length; i++) {
                if (i == swapIndex1 || i == swapIndex2)
                    continue;
                if ((influences[variableOrdering[i]][variableOrdering[swapIndex1]] || influences[variableOrdering[swapIndex1]][variableOrdering[i]])
                        && (influences[variableOrdering[i]][variableOrdering[swapIndex2]] || influences[variableOrdering[swapIndex2]][variableOrdering[i]]))
                    continue;
                if (influences[variableOrdering[i]][variableOrdering[swapIndex1]]
                        || influences[variableOrdering[swapIndex1]][variableOrdering[i]])
                    totalDistance = totalDistance
                            - Math.max(i - swapIndex1, swapIndex1 - i)
                            * Math.max(i - swapIndex1, swapIndex1 - i)
                            + Math.max(i - swapIndex2, swapIndex2 - i)
                            * Math.max(i - swapIndex2, swapIndex2 - i);
                if (influences[variableOrdering[i]][variableOrdering[swapIndex2]]
                        || influences[variableOrdering[swapIndex2]][variableOrdering[i]])
                    totalDistance = totalDistance
                            - Math.max(i - swapIndex2, swapIndex2 - i)
                            * Math.max(i - swapIndex2, swapIndex2 - i)
                            + Math.max(i - swapIndex1, swapIndex1 - i)
                            * Math.max(i - swapIndex1, swapIndex1 - i);
            }
            if (totalDistance < oldTotalDistance) {
                tmpVariable = variableOrdering[swapIndex1];
                variableOrdering[swapIndex1] = variableOrdering[swapIndex2];
                variableOrdering[swapIndex2] = tmpVariable;
                oldTotalDistance = totalDistance;
            } else {
                totalDistance = oldTotalDistance;
            }
        }
        return oldTotalDistance;
    }
}
