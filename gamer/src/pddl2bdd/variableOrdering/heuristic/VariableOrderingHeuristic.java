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

import java.util.*;
import java.io.*;

/**
 *
 * @author Peter Kissmann
 * @version 2.0
 */
public abstract class VariableOrderingHeuristic {
    // Random rnd = new Random(System.currentTimeMillis());
    Random rnd;

    public VariableOrderingHeuristic() {
    	File file = new File("seed");
    	if (file.exists()) {
			try {
				BufferedReader bufferedReader = new BufferedReader(new FileReader("seed"));
				String line;
				if ((line = bufferedReader.readLine()) != null) {
					long seed = Long.parseLong(line);
					rnd = new Random(seed);
				} else {
					rnd = new Random(0);
				}
			} catch (Exception e) {
				System.err.println("Error: " + e.getMessage());
				e.printStackTrace();
				System.exit(1);
			}
    	} else {
    		rnd = new Random(0);
    	}
    }

    public abstract int[] findVariableOrdering(LinkedList<LinkedList<String>> partitions);
}
