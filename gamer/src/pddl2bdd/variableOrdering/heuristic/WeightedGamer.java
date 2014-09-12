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
public class WeightedGamer extends VariableOrderingHeuristic {
	private boolean bidir;
	private boolean inverse;

	public WeightedGamer(boolean bidir, boolean inverse) {
		this.bidir = bidir;
		this.inverse = inverse;
	}

	public WeightedGamer(boolean bidir) {
		this.bidir = bidir;
		inverse = false;
	}

	public WeightedGamer() {
		bidir = false;
		inverse = false;
	}

    public int[] findVariableOrdering(LinkedList<LinkedList<String>> partitions) {
    	CausalGraph cg = new CausalGraph(partitions, bidir, false);
    	int[][] influences = new int[partitions.size()][partitions.size()];
    	for (int i = 0; i < influences.length; i++) {
    		CausalGraphNode node = cg.getVariable(i);
    		CausalGraphNode succ;
    		for (int j = 0; j < node.getNumberOfSuccessors(); j++) {
    			succ = node.getSuccessor(j);
    			influences[i][succ.getVariable()]++;
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

    private long findOneVariableOrdering(int[][] influences,
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
            	if (influences[variableOrdering[i]][variableOrdering[j]] != 0) {
            		totalDistance += (i - j) * (i - j) * influences[variableOrdering[i]][variableOrdering[j]] * influences[variableOrdering[i]][variableOrdering[j]];
            	}
            	if (influences[variableOrdering[j]][variableOrdering[i]] != 0) {
            		totalDistance += (i - j) * (i - j) * influences[variableOrdering[j]][variableOrdering[i]] * influences[variableOrdering[j]][variableOrdering[i]];
                }
            }
        }
        System.out.println("initial distance: " + totalDistance);
        for (int i = 0; i < variableOrdering.length; i++) {
        	System.out.print(" " + variableOrdering[i]);
        }
        System.out.println();
        oldTotalDistance = totalDistance;
        for (int counter = 0; counter < 50000; counter++) {
            swapIndex1 = rnd.nextInt(variableOrdering.length);
            swapIndex2 = rnd.nextInt(variableOrdering.length);
            // System.out.println(influences[variableOrdering[swapIndex1]][variableOrdering[swapIndex2]]);
            for (int i = 0; i < variableOrdering.length; i++) {
                if (i == swapIndex1 || i == swapIndex2)
                    continue;
                if (influences[variableOrdering[i]][variableOrdering[swapIndex1]] != 0) {
                	totalDistance = totalDistance
                			- (i - swapIndex1) * (i - swapIndex1) * influences[variableOrdering[i]][variableOrdering[swapIndex1]] * influences[variableOrdering[i]][variableOrdering[swapIndex1]]
                			+ (i - swapIndex2) * (i - swapIndex2) * influences[variableOrdering[i]][variableOrdering[swapIndex1]] * influences[variableOrdering[i]][variableOrdering[swapIndex1]];
                }
                if (influences[variableOrdering[swapIndex1]][variableOrdering[i]] != 0) {
                	totalDistance = totalDistance
                			- (i - swapIndex1) * (i - swapIndex1) * influences[variableOrdering[swapIndex1]][variableOrdering[i]] * influences[variableOrdering[swapIndex1]][variableOrdering[i]]
                			+ (i - swapIndex2) * (i - swapIndex2) * influences[variableOrdering[swapIndex1]][variableOrdering[i]] * influences[variableOrdering[swapIndex1]][variableOrdering[i]];
                }
                if (influences[variableOrdering[i]][variableOrdering[swapIndex2]] != 0) {
                	totalDistance = totalDistance
                			- (i - swapIndex2) * (i - swapIndex2) * influences[variableOrdering[i]][variableOrdering[swapIndex2]] * influences[variableOrdering[i]][variableOrdering[swapIndex2]]
                			+ (i - swapIndex1) * (i - swapIndex1) * influences[variableOrdering[i]][variableOrdering[swapIndex2]] * influences[variableOrdering[i]][variableOrdering[swapIndex2]];
                }
                if (influences[variableOrdering[swapIndex2]][variableOrdering[i]] != 0) {
                	totalDistance = totalDistance
                			- (i - swapIndex2) * (i - swapIndex2) * influences[variableOrdering[swapIndex2]][variableOrdering[i]] * influences[variableOrdering[swapIndex2]][variableOrdering[i]]
                			+ (i - swapIndex1) * (i - swapIndex1) * influences[variableOrdering[swapIndex2]][variableOrdering[i]] * influences[variableOrdering[swapIndex2]][variableOrdering[i]];
                }
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
