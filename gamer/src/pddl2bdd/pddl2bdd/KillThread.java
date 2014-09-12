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

package pddl2bdd.pddl2bdd;

import net.sf.javabdd.*;

/**
 * 
 * @author kissmann
 * @version 2.0
 */
public class KillThread extends Thread {
	private long runtime;
	private BDDFactory factory;

	public KillThread(long runtime, BDDFactory factory) {
		this.runtime = runtime;
		this.factory = factory;
	}

	@Override
	public void run() {
		try {
			Thread.sleep(runtime);
			System.out.println("Last backward step took longer than allowed!");
			System.out.println("Restarting planner with only forward search.");
        	System.out.println("peak nodecount: " + factory.getNodeTableSize());
			factory.printStat();
			System.exit(1);
		} catch (InterruptedException ie) {
			System.out.println("Last backward step successfully finished in time.");
		}
	}
}
