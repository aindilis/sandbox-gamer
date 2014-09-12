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

import java.util.*;

import pddl2bdd.parser.GroundedPDDLParser;
import pddl2bdd.parser.logic.*;
import pddl2bdd.util.Maths;
import pddl2bdd.util.Time;
import pddl2bdd.PDDL2BDD;
import net.sf.javabdd.*;

import java.io.*;

/**
 * This class creates BDDs for given domains and problems. It binds together
 * some internal variables so that for example 3 internal binary variables can
 * stand for up to 8 true binary ones - in case that these are mutually
 * exclusive. To do this, in this version the user has to give a legal
 * partitioning.<br>
 * An efficient order of variables is used: one variable of the predecessor
 * state and the corresponding variable of the successor state are used
 * alternately.<br>
 * <br>
 * This class not only creates the BDDs but also allows (bidirectional)
 * symbolic Dijkstra search. It also performs solution reconstruction and
 * writes an optimal plan into the file "plan_output".
 * 
 * @author Peter Kissmann
 * @version 2.0
 */
public class MakeFDDDijkstra {
	public BDDFactory factory;
	private int numberOfVariables; // number of boolean variables
	private BDDVarSet cube; // cube of S
	private BDDVarSet cubep; // cube of S'
	private BDD cubeBDD;
	private BDD cubepBDD;
	private BDDPairing s2sp; // permutation for S -> S'
	private BDDPairing sp2s; // permutation for S' -> S
	private BDD[] variables; // BDD variables
	private BDD[] not_variables; // negation of the BDD variables
	private BDD[] S; // S variables (current state)
	private BDD[] Sp; // S' variables (next state)
	private BDD init; // initial state
	private HashMap<Integer, LinkedList<BDD>> t; // transition relation (actions)
	private BDD trueGoal; // bdd representing the true (i.e. not simplified) goal-state
	private LinkedList<LinkedList<String>> partitionedVariables; // partition of the boolean variables as given by the user
	private LinkedList<String> nAryVariables; // list of all n-ary variables
	private LinkedList<BDD> nAryVariablesPreBDDs; // bdds representing the n-ary variables for the current state
	private LinkedList<BDD> nAryVariablesEffBDDs; // bdds representing the n-ary variables for the next state
	private HashMap<Integer, LinkedList<String>> actionNames; // list of all possible actions (resp. their names)
	private LinkedList<Integer> actionCosts;

	private int maxCost; // maximal action-cost
    private boolean autoReorder = false;
    private int nextReorderingLimit;
    private boolean allowReordering;

	/**
	 * Creates new BDDs for the given domain and problem. <br>
	 * <br>
	 * In this constructor new BDDs for the given domain and problem will be
	 * created. <br>
	 * First, the specified number of variables will be allocated. It is
	 * important that the number of variables equals twice the number of
	 * variables needed for one state, as variables are needed for both, one
	 * state and its successor (or predecessor in backward search). <br>
	 * Next, BDDs for the transition relation will be generated. Here the
	 * actions from the domain will be taken and for each action a BDD will be
	 * created as the disjunction takes quite an amount of time sometimes. This
	 * has the advantage that every transition-BDD corresponds directly to one
	 * action and thus an action-plan can be returned after a search. <br>
	 * Next, a BDD for the goal-description is created. First of all, a BDD for
	 * the given goal from the problem will be generated. <br>
	 * Finally, a BDD for the initial state, given in the problem, is created.
	 * 
	 * @param domain
	 *            The root of the domain, represented as a tree
	 * @param problem
	 *            The root of the problem, represented as a Tree
	 * @param partitions
	 *            The partition of the variables. In this class we do not use
	 *            true boolean variables to represent the states, but put as
	 *            many as possible together - variables that are mutually
	 *            exclusive can be together in one partition. If exactly one of
	 *            the variables in one partition can be true, everything is
	 *            fine. If it also can happen that none of these are true, we
	 *            need an extra variable (something like "none-of-these") to
	 *            represent the case that none of the variables of this
	 *            partition are true. This extra variable has to be at the last
	 *            one of the partition. Note also that all variable-names have
	 *            to be unique.
	 * @param numberOfVars
	 *            The number of boolean variables to be used (equals twice the
	 *            number of boolean variables needed for one state).
	 * @param library
	 *            The BDD library used.
	 */
	public MakeFDDDijkstra(LinkedList<LinkedList<String>> partitions,
			int numberOfVars, String library) {
		this.numberOfVariables = numberOfVars;
		this.partitionedVariables = partitions;

		// allocate BDD vars
		System.out.println("   creating variables ...");
		factory = BDDFactory.init(library, 16000000, 16000000);
		factory.setVarNum(numberOfVariables);
		variables = new BDD[numberOfVariables];
		not_variables = new BDD[numberOfVariables];
		for (int i = 0; i < numberOfVariables; i++) {
			BDD variable = factory.ithVar(i);
			variables[i] = variable;
			not_variables[i] = variable.not();
		}

        // preparing reordering - assigning groups to be kept together
        ListIterator<LinkedList<String>> partItBlock = partitions.listIterator();
        int blockCounter = 0;
        while (partItBlock.hasNext()) {
            int size = 2 * Maths.log2(partItBlock.next().size());
            factory.addVarBlock(blockCounter, blockCounter + size, true);
            blockCounter += size;
        }
        /*if (PDDL2BDD.REORDERING_TIME > 0.0 || PDDL2BDD.REORDERING_STEPS >= 0) {
            System.out.println("Starting dynamic reordering");
            factory.autoReorder(BDDFactory.REORDER_SIFT);
            autoReorder = true;
            }*/
        nextReorderingLimit = -1;
        try {
            File nextLimitFile = new File("nextReorderingLimit");
            if (nextLimitFile.exists()) {
                String line;
                BufferedReader bufferedReader = new BufferedReader(new FileReader("variableOrdering"));
                String lastLine = null;
                while ((line = bufferedReader.readLine()) != null) {
                    lastLine = line;
                }
                String[] lineParts = lastLine.split(" ");
                int[] order = new int[numberOfVariables];
                for (int i = 0; i < numberOfVariables; i++) {
                    order[i] = Integer.parseInt(lineParts[i]);
                }
                factory.setVarOrder(order);
                System.out.print("Setting ordering");
                for (int i = 0; i < numberOfVariables; i++) {
                    System.out.print(" " + order[i]);
                }
                System.out.println();
                bufferedReader = new BufferedReader(new FileReader("reorderingsRemaining"));
                int reordersLeft = -1;
                while ((line = bufferedReader.readLine()) != null) {
                    reordersLeft = Integer.parseInt(line);
                }
                if (reordersLeft <= 0) {
                    System.out.println("Not starting dynamic reordering, as all steps already done in bidirectional search");
                    allowReordering = false;
                } else {
                    bufferedReader = new BufferedReader(new FileReader("nextReorderingLimit"));
                    while ((line = bufferedReader.readLine()) != null) {
                        nextReorderingLimit = Integer.parseInt(line);
                    }
                    // start dynamic reordering delayed only (to after the transition relation and stuff was read)
                    //System.out.println("Starting dynamic reordering, first one when " + nextLimit + " nodes allocated");
                    //factory.autoReorder(BDDFactory.REORDER_SIFT, nextLimit);
                    factory.setReorderTimes(reordersLeft);
                    allowReordering = true;
                }
            } else {
                factory.setReorderTimes(PDDL2BDD.REORDERING_STEPS);
				FileWriter writer = new FileWriter("nextReorderingLimit");
                writer.write(factory.reorderVerbose(0) + "\n");
				writer.flush();
				writer.close();
                writer = new FileWriter("reorderingsRemaining");
                writer.write(PDDL2BDD.REORDERING_STEPS + "\n");
                writer.flush();
                writer.close();
                writer = new FileWriter("variableOrdering");
                for (int i = 0; i < numberOfVariables; i++) {
                    Integer iint = new Integer(i);
                    writer.write(iint.toString());
                    if (i < numberOfVariables - 1)
                        writer.write(" ");
                }
                writer.write("\n");
                writer.flush();
                writer.close();
                // starting dynamic reordering immediately - maybe better delay it?
                if (PDDL2BDD.REORDERING_STEPS > 0) {
                    //System.out.println("Starting dynamic reordering with default settings");
                    //factory.autoReorder(BDDFactory.REORDER_SIFT);
                    //autoReorder = true;
                    allowReordering = true;
                } else {
                    allowReordering = false;
                }
            }
        } catch (Exception e) {
            System.err.println("Error: " + e.getMessage());
            e.printStackTrace();
            System.exit(1);
        }


		// get current / next state variables
		S = new BDD[numberOfVariables / 2];
		Sp = new BDD[numberOfVariables / 2];
		int[] preVars = new int[numberOfVariables / 2];
		int[] effVars = new int[numberOfVariables / 2];
		for (int i = 0; i < numberOfVariables / 2; i++) {
			S[i] = variables[i * 2];
			preVars[i] = i * 2;
			Sp[i] = variables[i * 2 + 1];
			effVars[i] = i * 2 + 1;
		}

		// S and S' cube:
		cube = factory.makeSet(preVars);
		cubep = factory.makeSet(effVars);
		cubeBDD = cube.toBDD();
		cubepBDD = cubep.toBDD();

		// S -> S' permutation and S' -> S permutation
		s2sp = factory.makePair();
		sp2s = factory.makePair();
		for (int i = 0; i < numberOfVariables / 2; i++) {
			s2sp.set(i * 2, i * 2 + 1);
			sp2s.set(i * 2 + 1, i * 2);
		}

		createNAryVariables();
		System.out.println("   done.");

		ListIterator<LinkedList<String>> partIt = partitions.listIterator();
		int arraySize = 0;
		while (partIt.hasNext())
			arraySize += partIt.next().size();
		boolean[] unusedVarIndices = new boolean[arraySize];

		// build the transition relation
		actionNames = new HashMap<Integer, LinkedList<String>>();
		t = new HashMap<Integer, LinkedList<BDD>>();
		actionCosts = new LinkedList<Integer>();
		boolean bddsStored = false;
		File file = new File("goal");
		if (file.exists()) {
			bddsStored = true;
			System.out.println("   loading transition relation ...");
			maxCost = -1;
			int cost;
			file = new File(".");
			FilenameFilter filter = new FilenameFilter() {
				public boolean accept(File dir, String name) {
					return name.startsWith("transition");
				}
			};
			String[] transFiles = file.list(filter);
			for (int i = 0; i < transFiles.length; i++) {
				String[] fileParts = transFiles[i].split("_", 3);
				cost = Integer.parseInt(fileParts[1]);
				if (!actionCosts.contains(cost)) {
					actionCosts.add(cost);
					actionNames.put(cost, new LinkedList<String>());
					t.put(cost, new LinkedList<BDD>());
				}
				if (cost > maxCost)
					maxCost = cost;
				try {
					BDD actionBDD = factory.load(transFiles[i]);
					t.get(cost).addLast(actionBDD);
					actionNames.get(cost).addLast(fileParts[2]);
				} catch (Exception e) {
					System.err.println("Error: " + e.getMessage());
					e.printStackTrace();
					System.exit(1);
				}
			}
			Collections.sort(actionCosts);
			if (actionCosts.getFirst() == 0)
				actionCosts.removeFirst();
		} else {
			System.out.println("   building transition relation ...");
			ListIterator<Action> actionIt;
			maxCost = -1;
			actionIt = GroundedPDDLParser.actions.listIterator();
			while (actionIt.hasNext()) {
				int cost = actionIt.next().getCost();
				if (!actionCosts.contains(cost)) {
					actionCosts.add(cost);
					actionNames.put(cost, new LinkedList<String>());
					t.put(cost, new LinkedList<BDD>());
				}
				if (cost > maxCost)
					maxCost = cost;
			}
			Collections.sort(actionCosts);
			if (actionCosts.getFirst() == 0)
				actionCosts.removeFirst();
			actionIt = GroundedPDDLParser.actions.listIterator();
			while (actionIt.hasNext()) {
				Action action = actionIt.next();
				BDD actionBDD = action.createBDD(factory, nAryVariables,
						nAryVariablesPreBDDs, nAryVariablesEffBDDs, partitions,
						variables, unusedVarIndices);
				t.get(action.getCost()).addLast(actionBDD);
				actionNames.get(action.getCost()).addLast(action.getName());
			}
		}
		System.out.println("   done.");

		// build initial state
		if (bddsStored) {
			System.out.println("   loading initial state ...");
			try {
				init = factory.load("init");
			} catch (Exception e) {
				System.err.println("Error: " + e.getMessage());
				e.printStackTrace();
				System.exit(1);
			}
		} else {
			System.out.println("   building initial state ...");
			initialize();
		}
		System.out.println("   done.");

		// build the goal
		if (bddsStored) {
			System.out.println("   loading goal states ...");
			try {
				trueGoal = factory.load("goal");
			} catch (Exception e) {
				System.err.println("Error: " + e.getMessage());
				e.printStackTrace();
				System.exit(1);
			}
		} else {
			System.out.println("   building goal states ...");
			trueGoal = GroundedPDDLParser.goalDescription.createBDD(factory,
                                                                    nAryVariables, nAryVariablesPreBDDs, nAryVariablesEffBDDs, false, unusedVarIndices);
		}
		System.out.println("   done.");

        /* Since IPC 2014 version, no need to store BDDs on disk
         * when using (bidirectional) Dijkstra search. Thus, preventing
         * writing of any BDDs here in order to improve speed (at least
         * in pre-competition tests, connection to hard drive was
         * extremely slow and this step cost a lot of time)
         */
        bddsStored = true;
		if (!bddsStored) {
			// write transition relation to disk (in case of killed backward search)
			String baseFilename = "transitionRelation_";
			Iterator<Integer> keyIt = t.keySet().iterator();
			while (keyIt.hasNext()) {
				int key = keyIt.next();
				String baseFilename2 = baseFilename + key + "_";
				int counter = 0;
				ListIterator<BDD> bddIt = t.get(key).listIterator();
				while (bddIt.hasNext()) {
					String filename = baseFilename2 + actionNames.get(key).get(counter);
					try {
						factory.save(filename, bddIt.next());
					} catch (Exception e) {
						System.err.println("Error: " + e.getMessage());
						e.printStackTrace();
						System.exit(1);
					}
					counter++;
				}
			}

			// write initial state to disk
			try {
				factory.save("init", init);
			} catch (Exception e) {
				System.err.println("Error: " + e.getMessage());
				e.printStackTrace();
				System.exit(1);
			}

			// write goal condition to disk
			try {
				factory.save("goal", trueGoal);
			} catch (Exception e) {
				System.err.println("Error: " + e.getMessage());
				e.printStackTrace();
				System.exit(1);
			}
		}
	}

	private void createNAryVariables() {
		int currentVariable = 0;
		BDD[][] partVariables;
		BDD tmp;
		nAryVariables = new LinkedList<String>();
		nAryVariablesPreBDDs = new LinkedList<BDD>();
		nAryVariablesEffBDDs = new LinkedList<BDD>();
		for (int i = 0; i < partitionedVariables.size(); i++) {
			int size = partitionedVariables.get(i).size();
			int numberOfVars = Maths.log2(size);
			for (int j = 0; j < size; j++) {
				nAryVariables.add(partitionedVariables.get(i).get(j));
				partVariables = getVariables(currentVariable, numberOfVars, j);
				if (numberOfVars > 1) {
					BDD variablePreBDD = factory.one();
					BDD variableEffBDD = factory.one();
					for (int k = 0; k < numberOfVars; k++) {
						tmp = variablePreBDD;
						variablePreBDD = tmp.and(partVariables[0][k]);
						if (!tmp.equals(factory.one()))
							tmp.free();
						tmp = variableEffBDD;
						variableEffBDD = tmp.and(partVariables[1][k]);
						if (!tmp.equals(factory.one()))
							tmp.free();
					}
					nAryVariablesPreBDDs.add(variablePreBDD);
					nAryVariablesEffBDDs.add(variableEffBDD);
				} else {
					nAryVariablesPreBDDs.add(partVariables[0][0]);
					nAryVariablesEffBDDs.add(partVariables[1][0]);
				}
			}
			currentVariable += numberOfVars;
		}
	}

	private BDD[][] getVariables(int startingVariable, int numberOfVars,
			int value) {
		int remainingValue = value;
		BDD[][] returnVariables = new BDD[2][numberOfVars];
		for (int i = 0; i < numberOfVars; i++) {
			if (remainingValue >= Math.pow(2, numberOfVars - i - 1)) {
				returnVariables[0][i] = variables[(startingVariable + i) * 2];
				returnVariables[1][i] = variables[(startingVariable + i) * 2 + 1];
				remainingValue = remainingValue
						- (int) Math.pow(2, numberOfVars - i - 1);
			} else {
				returnVariables[0][i] = not_variables[(startingVariable + i) * 2];
				returnVariables[1][i] = not_variables[(startingVariable + i) * 2 + 1];
			}
		}
		if (remainingValue != 0) {
			System.out
			.println("ERROR: n-ary variable could not be created using binary variables!");
			System.exit(1);
		}
		return returnVariables;
	}

	private void initialize() {
		LinkedList<String> initialVariables;
		BDD tmp;

		init = factory.one();
		initialVariables = new LinkedList<String>();
		ListIterator<Predicate> initIt = GroundedPDDLParser.initialState
				.listIterator();
		while (initIt.hasNext()) {
			Predicate pred = initIt.next();
			String name = pred.getName();
			initialVariables.add(name);
			tmp = init;
			init = nAryVariablesPreBDDs.get(nAryVariables.indexOf(name)).and(
					init);
			tmp.free();
		}
		for (int i = 0; i < partitionedVariables.size(); i++) {
			int size = partitionedVariables.get(i).size();
			boolean variableInserted = false;
			for (int j = 0; j < size; j++) {
				if (initialVariables.contains(partitionedVariables.get(i)
						.get(j))) {
					variableInserted = true;
					break;
				}
			}
			if (!variableInserted) {
				if (partitionedVariables.get(i).getLast().startsWith(
						"none-of-these")) {
					tmp = init;
					init = nAryVariablesPreBDDs.get(
							nAryVariables.indexOf(partitionedVariables.get(i)
									.getLast())).and(init);
					tmp.free();
				} else {
					System.out
					.println("Error: no variable of group "
							+ i
							+ " though there is no \'none-of-these\'-variable!");
					System.exit(1);
				}
			}
		}
	}

	/**
	 * Cleans up in that it de-references all BDDs.
	 */
	public void cleanup() {
		cubeBDD.free();
		cubepBDD.free();
		cube.free();
		cubep.free();
		s2sp = null;
		sp2s = null;
		Collection<LinkedList<BDD>> t_collection = t.values();
		Iterator<LinkedList<BDD>> t_coll_it = t_collection.iterator();
		while (t_coll_it.hasNext()) {
			LinkedList<BDD> t_list = t_coll_it.next();
			ListIterator<BDD> t_list_it = t_list.listIterator();
			while (t_list_it.hasNext()) {
				t_list_it.next().free();
				t_list_it.remove();
			}
			t_coll_it.remove();
		}
		init.free();
		trueGoal.free();
		int counter = 0;
		for (int i = 0; i < partitionedVariables.size(); i++) {
			int size = partitionedVariables.get(i).size();
			if (size <= 2) {
				counter += size;
				continue;
			} else {
				for (int j = 0; j < size; j++) {
					nAryVariablesPreBDDs.get(counter).free();
					counter++;
				}
			}
		}
		for (int i = 0; i < numberOfVariables; i++) {
			variables[i].free();
			not_variables[i].free();
		}
        System.out.println("peak nodecount: " + factory.getNodeTableSize());
		factory.done();
	}

	private BDD image(int cost, BDD from, BDDVarSet varSet) {
		return image(cost, from, factory.one(), varSet);
	}

	private BDD image(int cost, BDD from, BDD conjunct, BDDVarSet varSet) {
		BDD tmp1;
		BDD tmp2;
		LinkedList<BDD> t_cost = t.get(cost);
		Vector<BDD> array = new Vector<BDD>(t_cost.size());
		for (int i = 0; i < t_cost.size(); i++) {
			tmp1 = t_cost.get(i).relprod(from, varSet);
			array.add(tmp1.and(conjunct));
			tmp1.free();
		}

		for (int i = 0; i < array.size(); i++) {
			tmp1 = array.get(i);
			i++;
			if (i < array.size()) {
				tmp2 = array.get(i);
				array.add(tmp1.or(tmp2));
				tmp1.free();
				tmp2.free();
			}
		}
		return array.lastElement();
	}

	private Vector<Integer> searchStep(int index, HashMap<Integer, BDD> open, HashMap<Integer, Vector<BDD>> closed, Vector<BDD> closedTotal, BDD otherFrontier, BDDVarSet varSet, BDDPairing pairing) {
		BDD tmp1;
		BDD tmp2;
		BDD negatedReached;
		BDD to;
		BDD frontierTotal;
		Vector<Integer> ret = null;

		negatedReached = closedTotal.firstElement().not();
		tmp1 = open.remove(index);
		frontierTotal = tmp1.and(negatedReached);
		tmp1.free();
		if (frontierTotal.equals(factory.zero())) {
			negatedReached.free();
			return ret;
		}
		Vector<BDD> frontier = new Vector<BDD>();
		frontier.add(frontierTotal.id());

		// compare against other frontier
		tmp1 = frontierTotal.and(otherFrontier);
		if (!tmp1.equals(factory.zero())) {
			negatedReached.free();
			frontierTotal.free();
			frontier.firstElement().free();
			frontier.set(0, tmp1);
			closed.put(index, frontier);
			ret = new Vector<Integer>();
			ret.add(index);
			return ret;
		}

		if (t.containsKey(0)) {
			BDD tmp3;
			while (true) {
				tmp1 = image(0, frontier.lastElement(), varSet);
				to = tmp1.replace(pairing);
				tmp1.free();
				tmp1 = to.and(negatedReached);
				to.free();
				tmp2 = frontierTotal.not();
				tmp3 = tmp1.and(tmp2);
				tmp1.free();
				tmp2.free();
				if (tmp3.equals(factory.zero())) {
					break;
				}
				frontier.add(tmp3);

				// compare against other frontier
				tmp1 = tmp3.and(otherFrontier);
				if (!tmp1.equals(factory.zero())) {
					tmp1.free();
					negatedReached.free();
					closed.put(index, frontier);
					frontierTotal.free();
					ret = new Vector<Integer>();
					ret.add(index);
					return ret;
				}

				tmp1 = frontierTotal;
				frontierTotal = tmp1.or(frontier.lastElement());
				tmp1.free();
			}
		}

		negatedReached.free();
		tmp1 = closedTotal.firstElement();
        tmp2 = tmp1.or(frontierTotal);
		closedTotal.set(0, tmp2);
		tmp1.free();
		closed.put(index, frontier);

		int c;
		ListIterator<Integer> costIt = actionCosts.listIterator();
		while (costIt.hasNext()) {
			c = costIt.next();
			tmp1 = image(c, frontierTotal, varSet);
			to = tmp1.replace(pairing);
			tmp1.free();
			tmp1 = open.get(index + c);
			if (tmp1 == null) {
				open.put(index + c, to);
			} else {
				open.put(index + c, tmp1.or(to));
				tmp1.free();
				to.free();
			}

			// compare against other frontier
			tmp1 = open.get(index + c).and(otherFrontier);
			if (!tmp1.equals(factory.zero())) {
				tmp1.free();
				if (ret == null)
					ret = new Vector<Integer>();
				ret.add(index + c);
			}
		}
		frontierTotal.free();
		return ret;
	}

	private long MAX_STEP_TIME = 30 * 1000;
    private long INITIAL_MAX_STEP_TIME = 30 * 1000;
	private double TIME_INCREMENT = 2.5;

    private boolean WRITING_NECESSARY = false;

    private long getLastTotalReorderTime() {
        long lastTotalReorderTime = 0;
        File file = new File("totalReordTime");
        if (file.exists()) {
            try {
                BufferedReader bufferedReader = new BufferedReader(new FileReader("totalReordTime"));
                String line;
                while ((line = bufferedReader.readLine()) != null) {
                    lastTotalReorderTime = Long.parseLong(line);
                }
                bufferedReader.close();
            } catch (Exception e) {
                System.err.println("Error: " + e.getMessage());
                e.printStackTrace();
                System.exit(1);
            }
        }
        return lastTotalReorderTime;
    }

    private long getLastReorderTime() {
        long lastReorderTime = 0;
        File file = new File("lastReorderingTime");
        if (file.exists()) {
            try {
                int reordersRemaining = 0;
                file = new File("reorderingsRemaining");
                BufferedReader bufferedReader = new BufferedReader(new FileReader("reorderingsRemaining"));
                String line;
                while ((line = bufferedReader.readLine()) != null) {
                    reordersRemaining = Integer.parseInt(line);
                }
                bufferedReader.close();
                if (reordersRemaining > 0) {
                    bufferedReader = new BufferedReader(new FileReader("lastReorderingTime"));
                    while ((line = bufferedReader.readLine()) != null) {
                        lastReorderTime = Long.parseLong(line);
                    }
                    bufferedReader.close();
                }
            } catch (Exception e) {
                System.err.println("Error: " + e.getMessage());
                e.printStackTrace();
                System.exit(1);
            }
        }
        return lastReorderTime;
    }

	public void findPlanDijkstra(boolean bidir) {
        /*if (autoReorder && PDDL2BDD.REORDERING_STEPS == 0) {
            System.out.println("Stopping dynamic reordering");
            factory.disableReorder();
            autoReorder = false;
            }*/
		long dijkstraStartTime = System.currentTimeMillis();
		BDD tmp1;
		BDD intersection;
		HashMap<Integer, BDD> openForw = new HashMap<Integer, BDD>();
		HashMap<Integer, BDD> openBackw = new HashMap<Integer, BDD>();
		HashMap<Integer, Vector<BDD>> closedForw = new HashMap<Integer, Vector<BDD>>();
		HashMap<Integer, Vector<BDD>> closedBackw = new HashMap<Integer, Vector<BDD>>();
		Vector<BDD> closedForwTotal = new Vector<BDD>(); // Vector, so that it can be changed within searchStep
		Vector<BDD> closedBackwTotal = new Vector<BDD>(); // Vector, so that it can be changed within searchStep
		int gForw = 0;
		int gBackw = 0;
		int oldG;
		long lastForwTime = -1;
		long lastBackwTime = -1;
        long maxForwTime = -1;
		boolean stop = false;
		int optGForw = Integer.MAX_VALUE;
		int optVecIndexForw = Integer.MAX_VALUE;
		int optGBackw = Integer.MAX_VALUE;
		int optVecIndexBackw = Integer.MAX_VALUE;
		BDD optIntersection = null;
		int optCost = Integer.MAX_VALUE;
		Vector<Integer> nonEmptyCut = null;
		LinkedList<Integer> storedOpenForwSteps = new LinkedList<Integer>();
		LinkedList<Integer> storedOpenBackwSteps = new LinkedList<Integer>();

		String dijkstraDir = new String("dijkstraSteps/");
        if (WRITING_NECESSARY) {
		File dirCheck = new File(dijkstraDir);
		if (dirCheck.exists() && dirCheck.isDirectory()) {
			if (bidir) {
				System.out.println("Switching to forward search, as directory \"dijkstraSteps\" exists, which should hold BDDs of a previous (bidirectional) Dijkstra search.");
				bidir = false;
			}
			System.out.println("   loading BDDs from previous run...");
			File file = new File(dijkstraDir + "closedForw.txt");
			LinkedList<Integer> stepsClosed = new LinkedList<Integer>();
			if (file.exists()) {
				try {
					BufferedReader bufferedReader = new BufferedReader(
							new FileReader(dijkstraDir + "closedForw.txt"));
					String line;
					String[] lineParts;
					int step;
					while ((line = bufferedReader.readLine()) != null) {
						lineParts = line.split(" ");
						step = Integer.parseInt(lineParts[0]);
						stepsClosed.add(step);
						if (!lineParts[1].equals("-1")) {
							Vector<BDD> bfsLayers = new Vector<BDD>(lineParts.length - 1);
							for (int i = 1; i < lineParts.length; i++) {
								bfsLayers.add(factory.load(dijkstraDir + "closedForw_" + step + "_" + lineParts[i]));
							}
							closedForw.put(step, bfsLayers);
						}
					}
					bufferedReader.close();
					closedForwTotal.clear();
					closedForwTotal.add(factory.load(dijkstraDir + "closedForwTotal"));
				} catch (Exception e) {
					System.err.println("Error: " + e.getMessage());
					e.printStackTrace();
					System.exit(1);
				}
			} else {
				closedForwTotal.clear();
				closedForwTotal.add(factory.zero());
			}
			file = new File(dijkstraDir + "openForw.txt");
			if (file.exists()) {
				try {
					BufferedReader bufferedReader = new BufferedReader(
							new FileReader(dijkstraDir + "openForw.txt"));
					String line;
					while ((line = bufferedReader.readLine()) != null) {
						int step = Integer.parseInt(line);
						if (!stepsClosed.contains(step)) {
							openForw.put(step, factory.load(dijkstraDir + "openForw_" + step));
						}
					}
					bufferedReader.close();
				} catch (Exception e) {
					System.err.println("Error: " + e.getMessage());
					e.printStackTrace();
					System.exit(1);
				}
			} else {
				System.err.println("Error: no file " + file.toString() + " not found!");
				System.exit(1);
			}

			file = new File(dijkstraDir + "closedBackw.txt");
			stepsClosed = new LinkedList<Integer>();
			if (file.exists()) {
				try {
					BufferedReader bufferedReader = new BufferedReader(
							new FileReader(dijkstraDir + "closedBackw.txt"));
					String line;
					String[] lineParts;
					int step;
					while ((line = bufferedReader.readLine()) != null) {
						lineParts = line.split(" ");
						step = Integer.parseInt(lineParts[0]);
						stepsClosed.add(step);
						if (!lineParts[1].equals("-1")) {
							Vector<BDD> bfsLayers = new Vector<BDD>(lineParts.length - 1);
							for (int i = 1; i < lineParts.length; i++) {
								bfsLayers.add(factory.load(dijkstraDir + "closedBackw_" + step + "_" + lineParts[i]));
							}
							closedBackw.put(step, bfsLayers);
						}
					}
					bufferedReader.close();
					closedBackwTotal.clear();
					closedBackwTotal.add(factory.load(dijkstraDir + "closedBackwTotal"));
				} catch (Exception e) {
					System.err.println("Error: " + e.getMessage());
					e.printStackTrace();
					System.exit(1);
				}
			} else {
				closedBackwTotal.clear();
				closedBackwTotal.add(trueGoal.id());
				Vector<BDD> vec = new Vector<BDD>();
				vec.add(trueGoal.id());
				closedBackw.put(0, vec);
			}
			file = new File(dijkstraDir + "openBackw.txt");
			if (file.exists()) {
				try {
					BufferedReader bufferedReader = new BufferedReader(
							new FileReader(dijkstraDir + "openBackw.txt"));
					String line;
					while ((line = bufferedReader.readLine()) != null) {
						int step = Integer.parseInt(line);
						if (!stepsClosed.contains(step)) {
							openBackw.put(step, factory.load(dijkstraDir + "openBackw_" + step));
						}
					}
					bufferedReader.close();
				} catch (Exception e) {
					System.err.println("Error: " + e.getMessage());
					e.printStackTrace();
					System.exit(1);
				}
			} else {
				System.err.println("Error: no file " + file.toString() + " not found!");
				System.exit(1);
			}

			try {
				BufferedReader bufferedReader = new BufferedReader(
						new FileReader(dijkstraDir + "gForw.txt"));
				String line;
				while ((line = bufferedReader.readLine()) != null) {
					gForw = Integer.parseInt(line);
				}
				bufferedReader.close();

				bufferedReader = new BufferedReader(
						new FileReader(dijkstraDir + "gBackw.txt"));
				while ((line = bufferedReader.readLine()) != null) {
					gBackw = Integer.parseInt(line);
				}
				bufferedReader.close();

				file = new File(dijkstraDir + "optGForw.txt");
				if (file.exists()) {
					bufferedReader = new BufferedReader(
							new FileReader(dijkstraDir + "optGForw.txt"));
					while ((line = bufferedReader.readLine()) != null) {
						optGForw = Integer.parseInt(line);
					}
					bufferedReader.close();
				}

				file = new File(dijkstraDir + "optGBackw.txt");
				if (file.exists()) {
					bufferedReader = new BufferedReader(
							new FileReader(dijkstraDir + "optGBackw.txt"));
					while ((line = bufferedReader.readLine()) != null) {
						optGBackw = Integer.parseInt(line);
					}
					bufferedReader.close();
				}

				file = new File(dijkstraDir + "optVecIndexForw.txt");
				if (file.exists()) {
					bufferedReader = new BufferedReader(
							new FileReader(dijkstraDir + "optVecIndexForw.txt"));
					while ((line = bufferedReader.readLine()) != null) {
						optVecIndexForw = Integer.parseInt(line);
					}
					bufferedReader.close();
				}

				file = new File(dijkstraDir + "optVecIndexBackw.txt");
				if (file.exists()) {
					bufferedReader = new BufferedReader(
							new FileReader(dijkstraDir + "optVecIndexBackw.txt"));
					while ((line = bufferedReader.readLine()) != null) {
						optVecIndexBackw = Integer.parseInt(line);
					}
					bufferedReader.close();
				}

				file = new File(dijkstraDir + "optIntersection");
				if (file.exists()) {
					optIntersection = factory.load(dijkstraDir + "optIntersection");
				}

				file = new File(dijkstraDir + "optCost.txt");
				if (file.exists()) {
					bufferedReader = new BufferedReader(
							new FileReader(dijkstraDir + "optCost.txt"));
					while ((line = bufferedReader.readLine()) != null) {
						optCost = Integer.parseInt(line);
					}
					bufferedReader.close();
				}
			} catch (Exception e) {
				System.err.println("Error: " + e.getMessage());
				e.printStackTrace();
				System.exit(1);
			}
			System.out.println("   done.");
			System.out.println("   Restarting with g-values " + gForw + " (forw) and " + gBackw + " (backw)");
		} else {
			closedForwTotal.add(factory.zero());
			if (bidir) {
				closedBackwTotal.add(factory.zero());
			} else {
				closedBackwTotal.add(trueGoal.id());
				Vector<BDD> vec = new Vector<BDD>();
				vec.add(trueGoal.id());
				closedBackw.put(0, vec);
			}
			openForw.put(gForw, init.id());
			openBackw.put(gBackw, trueGoal.id());

			try {
				dirCheck.mkdir();
				FileWriter writer = new FileWriter(dijkstraDir + "gBackw.txt");
				writer.write(gBackw + "\n");
				writer.flush();
				writer.close();
				writer = new FileWriter(dijkstraDir + "optGBackw.txt");
				writer.write(optGBackw + "\n");
				writer.flush();
				writer.close();
				writer = new FileWriter(dijkstraDir + "optGForw.txt");
				writer.write(optGForw + "\n");
				writer.flush();
				writer.close();
				writer = new FileWriter(dijkstraDir + "optVecIndexBackw.txt");
				writer.write(optVecIndexBackw + "\n");
				writer.flush();
				writer.close();
				writer = new FileWriter(dijkstraDir + "optVecIndexForw.txt");
				writer.write(optVecIndexForw + "\n");
				writer.flush();
				writer.close();
				writer = new FileWriter(dijkstraDir + "optCost.txt");
				writer.write(optCost + "\n");
				writer.flush();
				writer.close();
				factory.save(dijkstraDir + "closedBackwTotal", closedBackwTotal.get(0));
				if (closedBackw.size() > 0) {
					oldG = gBackw;
					Vector<BDD> closedToStore = closedBackw.get(oldG);
					writer = new FileWriter(dijkstraDir + "closedBackw.txt");
					writer.write(oldG + "");
					for (int i = 0; i < closedToStore.size(); i++) {
						factory.save(dijkstraDir + "closedBackw_" + oldG + "_" + i, closedToStore.get(i));
						writer.write(" " + i);
					}
					writer.write("\n");
					writer.flush();
					writer.close();
				}
				Iterator<Map.Entry<Integer, BDD>> openIt = openBackw.entrySet().iterator();
				writer = new FileWriter(dijkstraDir + "openBackw.txt");
				while (openIt.hasNext()) {
					Map.Entry<Integer, BDD> entry = openIt.next();
					if (!storedOpenBackwSteps.contains(entry.getKey())) {
						writer.write(entry.getKey() + "\n");
						storedOpenBackwSteps.add(entry.getKey());
					}
					factory.save(dijkstraDir + "openBackw_" + entry.getKey(), entry.getValue());
				}
				writer.flush();
				writer.close();

				writer = new FileWriter(dijkstraDir + "gForw.txt");
				writer.write(gForw + "\n");
				writer.flush();
				writer.close();
				factory.save(dijkstraDir + "closedForwTotal", closedForwTotal.get(0));
				if (closedForw.size() > 0) {
					oldG = gForw;
					Vector<BDD> closedToStore = closedForw.get(oldG);
					writer = new FileWriter(dijkstraDir + "closedForw.txt");
					writer.write(oldG + "");
					for (int i = 0; i < closedToStore.size(); i++) {
						factory.save(dijkstraDir + "closedForw_" + oldG + "_" + i, closedToStore.get(i));
						writer.write(" " + i);
					}
					writer.write("\n");
					writer.flush();
					writer.close();
				}
				openIt = openForw.entrySet().iterator();
				writer = new FileWriter(dijkstraDir + "openForw.txt");
				while (openIt.hasNext()) {
					Map.Entry<Integer, BDD> entry = openIt.next();
					if (!storedOpenForwSteps.contains(entry.getKey())) {
						writer.write(entry.getKey() + "\n");
						storedOpenForwSteps.add(entry.getKey());
					}
					factory.save(dijkstraDir + "openForw_" + entry.getKey(), entry.getValue());
				}
				writer.flush();
				writer.close();
			} catch (Exception e) {
				System.err.println("Error: " + e.getMessage());
				e.printStackTrace();
				System.exit(1);
			}
			tmp1 = openBackw.get(gBackw).replace(sp2s);
			intersection = openForw.get(gForw).and(tmp1);
			tmp1.free();
			if (!intersection.equals(factory.zero())) {
				intersection.free();
				stop = true;
			}
		}
		} else {
			closedForwTotal.add(factory.zero());
			if (bidir) {
				closedBackwTotal.add(factory.zero());
			} else {
				closedBackwTotal.add(trueGoal.id());
				Vector<BDD> vec = new Vector<BDD>();
				vec.add(trueGoal.id());
				closedBackw.put(0, vec);
			}
			openForw.put(gForw, init.id());
			openBackw.put(gBackw, trueGoal.id());
        }

        if (allowReordering && !autoReorder) {
            if (nextReorderingLimit < 0) {
                System.out.println("Starting dynamic reordering with default settings");
                factory.autoReorder(BDDFactory.REORDER_SIFT);
            } else {
                System.out.println("Starting dynamic reordering, first one when " + nextReorderingLimit + " nodes allocated");
                factory.autoReorder(BDDFactory.REORDER_SIFT, nextReorderingLimit);
                nextReorderingLimit = -1;
            }
            autoReorder = true;
        }

        int step = 0;
		while (!stop && gForw + gBackw < optCost) {
			if (optCost == Integer.MAX_VALUE)
				System.out.println("so far, no plan found");
			else
				System.out.println("best plan so far has cost: " + optCost);

            /*
            if (allowReordering) {
                if (nextReorderingLimit < 0) {
                    System.out.println("Starting dynamic reordering with default settings");
                    factory.autoReorder(BDDFactory.REORDER_SIFT);
                } else {
                    System.out.println("Starting dynamic reordering, first one when " + nextReorderingLimit + " nodes allocated");
                    factory.autoReorder(BDDFactory.REORDER_SIFT, nextReorderingLimit);
                    nextReorderingLimit = -1;
                }
                autoReorder = true;
            }
            */

			if (bidir && lastBackwTime < lastForwTime) {
                long startTime = System.currentTimeMillis();
                long lastTotalReorderTime = getLastTotalReorderTime();
				oldG = gBackw;
				System.out.println("Expanding bucket " + gBackw + " in backward direction");
                //System.out.println("size: " + (long) openBackw.get(gBackw).satCount(cubep));
				tmp1 = closedForwTotal.get(0).replace(s2sp);
				BDD openTmp = openBackw.get(gBackw).id();
                /*
                if (autoReorder)
                    factory.disableReorder();
                */
				//KillThread killThread = new KillThread(MAX_STEP_TIME, factory);
				//killThread.start();
                factory.setRuntimeLimit(factory.getRuntime() + MAX_STEP_TIME);
                BDD closedTmp = closedBackwTotal.get(0).id();
                try {
                    nonEmptyCut = searchStep(gBackw, openBackw, closedBackw, closedBackwTotal, tmp1, cubep, s2sp);
                } catch (Exception e) {
                    if (WRITING_NECESSARY) {
                        System.out.println("   Last backward step took longer than allowed!");
                        System.out.println("   Restarting planner with only forward search.");
                        System.out.println("   peak nodecount: " + factory.getNodeTableSize());
                        factory.printStat();
                        System.exit(1);
                    }
                    factory.unsetRuntimeLimit();
                    openBackw.put(gBackw, openTmp);
                    tmp1.free();
                    if (gBackw == 0) {
                        //if (closedBackwTotal.size() == 1 && closedBackwTotal.get(0).equals(factory.zero())) {
                        closedBackwTotal.get(0).free();
                        closedBackwTotal.set(0, trueGoal.id());
                        Vector<BDD> vec = new Vector<BDD>();
                        vec.add(trueGoal.id());
                        closedBackw.put(0, vec);
                    } else {
                        if (closedBackwTotal.get(0) != null)
                            closedBackwTotal.get(0).free();
                        closedBackwTotal.set(0, closedTmp);
                        Vector<BDD> closedVec = closedBackw.remove(gBackw);
                        if (closedVec != null) {
                            for (int i = 0; i < closedVec.size(); i++)
                                closedVec.get(i).free();
                        }
                    }
                    //System.out.println("Error: " + e.getMessage());
                    //e.printStackTrace();
                    System.out.println("   Last backward step took longer than allowed!");
                    System.out.println("   Stopping backward search");
                    lastBackwTime = Long.MAX_VALUE;
                    continue;
                }
                System.out.println("   Last backward step successfully finished in time.");
                factory.unsetRuntimeLimit();
				//killThread.interrupt();
                closedTmp.free();
                step++;
                /*if (autoReorder && PDDL2BDD.REORDERING_STEPS == step) {
                //if (autoReorder && factory.getReorderRuntime() > PDDL2BDD.REORDERING_TIME) {
                //if (autoReorder && factory.getReorderTimes() > 0) {
                    System.out.println("Stopping dynamic reordering");
                    factory.disableReorder();
                    autoReorder = false;
                    }*/
				tmp1.free();
				if (nonEmptyCut == null) {
					openTmp.free();
					Set<Integer> keySet = openBackw.keySet();
					if (keySet.size() == 0) {
						if (optCost == Integer.MAX_VALUE) {
							System.out.println("no plan!");
							long dijkstraEndTime = System.currentTimeMillis();
							System.out.println("Total time (Dijkstra): " + Time.printTime(dijkstraEndTime - dijkstraStartTime));
							return;
						} else {
							System.out.println("done in backward direction!");
							lastBackwTime = Long.MAX_VALUE;
							System.out.println("   took: " + Time.printTime(System.currentTimeMillis() - startTime));
						}
					} else {
						gBackw = Collections.min(keySet);
					}
					System.out.println("   next g value in backward direction: " + gBackw);
                    long currentTotalReorderTime = getLastTotalReorderTime();
					lastBackwTime = System.currentTimeMillis() - startTime;
                    lastBackwTime -= (currentTotalReorderTime - lastTotalReorderTime);
					System.out.println("   took: " + Time.printTime(lastBackwTime));
                    MAX_STEP_TIME = Math.max(INITIAL_MAX_STEP_TIME, (long) ((maxForwTime + getLastReorderTime()) * TIME_INCREMENT));
				} else if (nonEmptyCut.firstElement() == -1) { // last step took too long
					System.out.println("   last backward step took too long to finish; stopping backward search.");
					lastBackwTime = Long.MAX_VALUE;
					System.out.println(openBackw.size());
					Set<Integer> keySet = openBackw.keySet();
					if (keySet.size() != 0) {
						gBackw = Collections.min(keySet);
					}
					if (closedBackwTotal.firstElement().equals(factory.zero())) {
						closedBackwTotal.set(0, openTmp.id());
						Vector<BDD> vec = new Vector<BDD>();
						vec.add(openTmp);
						closedBackw.put(0, vec);
					} else {
						openTmp.free();
					}
				} else {
					openTmp.free();
					System.out.println("   non-empty cut in buckets " + nonEmptyCut);
					for (int nonEmptyIndex = 0; nonEmptyIndex < nonEmptyCut.size(); nonEmptyIndex++) {
						int nonEmptyCutBackw = nonEmptyCut.get(nonEmptyIndex);
						if (nonEmptyCutBackw == gBackw)
							intersection = closedBackw.get(gBackw).lastElement().replace(sp2s);
						else
							intersection = openBackw.get(nonEmptyCutBackw).replace(sp2s);
						Set<Integer> keySet = closedForw.keySet();
						Iterator<Integer> it = keySet.iterator();
						int smallestIndex = Integer.MAX_VALUE;
						int vecIndex = -1;
						BDD optTmp = null;
						while (it.hasNext()) {
							int index = it.next();
							if (index < gForw - actionCosts.getLast()) {
								continue;
							}
							if (index + nonEmptyCutBackw >= optCost) {
								continue;
							}
							if (index < smallestIndex) {
								Vector<BDD> vec = closedForw.get(index);
								for (int i = 0; i < vec.size(); i++) {
									tmp1 = intersection.and(vec.get(i));
									if (!tmp1.equals(factory.zero())) {
										if (optTmp != null)
											optTmp.free();
										optTmp = tmp1;
										smallestIndex = index;
										vecIndex = i;
									}
								}
							}
						}
						if (smallestIndex != Integer.MAX_VALUE) {
							optGForw = smallestIndex;
							optVecIndexForw = vecIndex;
							optGBackw = nonEmptyCutBackw;
							if (nonEmptyCutBackw == gBackw)
								optVecIndexBackw = closedBackw.get(gBackw).size() - 1;
							else
								optVecIndexBackw = 0;
							if (optIntersection != null)
								optIntersection.free();
							optIntersection = optTmp.replace(s2sp);
							optTmp.free();
							optCost = optGForw + optGBackw;
							System.out.println("   plan of cost " + optCost + " found");
						}
						intersection.free();
					}
					Set<Integer> keySet = openBackw.keySet();
					if (keySet.size() == 0) {
						if (optCost == Integer.MAX_VALUE) {
							System.out.println("no plan!");
							long dijkstraEndTime = System.currentTimeMillis();
							System.out.println("Total time (Dijkstra): " + Time.printTime(dijkstraEndTime - dijkstraStartTime));
							return;
						} else {
							System.out.println("done in backward direction!");
							lastBackwTime = Long.MAX_VALUE;
							System.out.println("   took: " + Time.printTime(System.currentTimeMillis() - startTime));
						}
					} else {
						gBackw = Collections.min(keySet);
					}
					System.out.println("   next g value in backward direction: " + gBackw);
                    long currentTotalReorderTime = getLastTotalReorderTime();
					lastBackwTime = System.currentTimeMillis() - startTime;
					lastBackwTime -= (currentTotalReorderTime - lastTotalReorderTime);
					System.out.println("   took: " + Time.printTime(lastBackwTime));
                    MAX_STEP_TIME = Math.max(INITIAL_MAX_STEP_TIME, (long) ((maxForwTime + getLastReorderTime()) * TIME_INCREMENT));
				}
                if (WRITING_NECESSARY) {
				try {
					FileWriter writer = new FileWriter(dijkstraDir + "gBackw.txt");
					writer.write(gBackw + "\n");
					writer.flush();
					writer.close();
					writer = new FileWriter(dijkstraDir + "optGBackw.txt");
					writer.write(optGBackw + "\n");
					writer.flush();
					writer.close();
					writer = new FileWriter(dijkstraDir + "optGForw.txt");
					writer.write(optGForw + "\n");
					writer.flush();
					writer.close();
					writer = new FileWriter(dijkstraDir + "optVecIndexBackw.txt");
					writer.write(optVecIndexBackw + "\n");
					writer.flush();
					writer.close();
					writer = new FileWriter(dijkstraDir + "optVecIndexForw.txt");
					writer.write(optVecIndexForw + "\n");
					writer.flush();
					writer.close();
					writer = new FileWriter(dijkstraDir + "optCost.txt");
					writer.write(optCost + "\n");
					writer.flush();
					writer.close();
					if (optIntersection != null) {
						factory.save(dijkstraDir + "optIntersection", optIntersection);
					}
					factory.save(dijkstraDir + "closedBackwTotal", closedBackwTotal.get(0));
					if (!closedBackw.containsKey(oldG)) {
						
					}
					writer = new FileWriter(dijkstraDir + "closedBackw.txt", true);
					if (!closedBackw.containsKey(oldG)) {
						writer.write(oldG + " -1");
					} else {
						Vector<BDD> closedToStore = closedBackw.get(oldG);
						writer.write(oldG + "");
						for (int i = 0; i < closedToStore.size(); i++) {
							factory.save(dijkstraDir + "closedBackw_" + oldG + "_" + i, closedToStore.get(i));
							writer.write(" " + i);
						}
						writer.write("\n");
						writer.flush();
						writer.close();
					}
					Iterator<Map.Entry<Integer, BDD>> openIt = openBackw.entrySet().iterator();
					writer = new FileWriter(dijkstraDir + "openBackw.txt", true);
					while (openIt.hasNext()) {
						Map.Entry<Integer, BDD> entry = openIt.next();
						if (!storedOpenBackwSteps.contains(entry.getKey())) {
							writer.write(entry.getKey() + "\n");
							storedOpenBackwSteps.add(entry.getKey());
						}
						factory.save(dijkstraDir + "openBackw_" + entry.getKey(), entry.getValue());
					}
					writer.flush();
					writer.close();
				} catch (Exception e) {
					System.err.println("Error: " + e.getMessage());
					e.printStackTrace();
					System.exit(1);
				}
                }
			} else {
                long startTime = System.currentTimeMillis();
                long lastTotalReorderTime = getLastTotalReorderTime();
				oldG = gForw;
				System.out.println("Expanding bucket " + gForw + " in forward direction");
                //System.out.println("size: " + (long) openForw.get(gForw).satCount(cubep));
                //openForw.get(oldG).printSet();
				tmp1 = closedBackwTotal.get(0).replace(sp2s);
                /*
                if (autoReorder)
                    factory.disableReorder();
                */
				nonEmptyCut = searchStep(gForw, openForw, closedForw, closedForwTotal, tmp1, cube, sp2s);
                step++;
                /*if (autoReorder && PDDL2BDD.REORDERING_STEPS == step) {
                //if (autoReorder && factory.getReorderRuntime() > PDDL2BDD.REORDERING_TIME) {
                //if (autoReorder && factory.getReorderTimes() > 0) {
                    System.out.println("stopping dynamic reordering");
                    factory.disableReorder();
                    autoReorder = false;
                    }*/
				tmp1.free();
				if (nonEmptyCut == null) {
					Set<Integer> keySet = openForw.keySet();
					if (keySet.size() == 0) {
						if (optCost == Integer.MAX_VALUE) {
							System.out.println("no plan!");
							long dijkstraEndTime = System.currentTimeMillis();
							System.out.println("Total time (Dijkstra): " + Time.printTime(dijkstraEndTime - dijkstraStartTime));
							return;
						} else {
							System.out.println("done in forward direction!");
							lastForwTime = Long.MAX_VALUE;
                            maxForwTime = Long.MAX_VALUE;
							System.out.println("   took: " + Time.printTime(System.currentTimeMillis() - startTime));
						}
					} else {
						gForw = Collections.min(keySet);
					}
					System.out.println("   next g value in forward direction: " + gForw);
                    long currentTotalReorderTime = getLastTotalReorderTime();
					lastForwTime = System.currentTimeMillis() - startTime;
					lastForwTime -= (currentTotalReorderTime - lastTotalReorderTime);
                    maxForwTime = Math.max(maxForwTime, lastForwTime);
					System.out.println("   took: " + Time.printTime(lastForwTime));
                    MAX_STEP_TIME = Math.max(INITIAL_MAX_STEP_TIME, (long) ((maxForwTime + getLastReorderTime()) * TIME_INCREMENT));
                    /*long lastReorderTime = getLastReorderTime();
                      if (lastForwTime + lastReorderTime > MAX_STEP_TIME / TIME_INCREMENT)
                      MAX_STEP_TIME = (long) ((lastForwTime + lastReorderTime) * TIME_INCREMENT);*/
				} else {
					System.out.println("   non-empty cut in buckets " + nonEmptyCut);
					for (int nonEmptyIndex = 0; nonEmptyIndex < nonEmptyCut.size(); nonEmptyIndex++) {
						int nonEmptyCutForw = nonEmptyCut.get(nonEmptyIndex);
						if (nonEmptyCutForw == gForw)
							intersection = closedForw.get(gForw).lastElement().replace(s2sp);
						else
							intersection = openForw.get(nonEmptyCutForw).replace(s2sp);
						Set<Integer> keySet = closedBackw.keySet();
						Iterator<Integer> it = keySet.iterator();
						int smallestIndex = Integer.MAX_VALUE;
						int vecIndex = -1;
						BDD optTmp = null;
						while (it.hasNext()) {
							int index = it.next();
							if (index < gBackw - actionCosts.getLast()) {
								continue;
							}
							if (index + nonEmptyCutForw >= optCost) {
								continue;
							}
							if (index < smallestIndex) {
								Vector<BDD> vec = closedBackw.get(index);
								for (int i = 0; i < vec.size(); i++) {
									tmp1 = intersection.and(vec.get(i));
									if (!tmp1.equals(factory.zero())) {
										if (optTmp != null)
											optTmp.free();
										optTmp = tmp1;
										smallestIndex = index;
										vecIndex = i;
									}
								}
							}
						}
						if (smallestIndex != Integer.MAX_VALUE) {
							optGBackw = smallestIndex;
							optVecIndexBackw = vecIndex;
							optGForw = nonEmptyCutForw;
							if (nonEmptyCutForw == gForw)
								optVecIndexForw = closedForw.get(gForw).size() - 1;
							else
								optVecIndexForw = 0;
							if (optIntersection != null)
								optIntersection.free();
							optIntersection = optTmp;
							optCost = optGBackw + optGForw;
							System.out.println("   plan of cost " + optCost + " found");
						}
						intersection.free();
					}
					Set<Integer> keySet = openForw.keySet();
					if (keySet.size() == 0) {
						if (optCost == Integer.MAX_VALUE) {
							System.out.println("no plan!");
							long dijkstraEndTime = System.currentTimeMillis();
							System.out.println("Total time (Dijkstra): " + Time.printTime(dijkstraEndTime - dijkstraStartTime));
							return;
						} else {
							System.out.println("done in forward direction!");
							lastForwTime = Long.MAX_VALUE;
                            maxForwTime = Long.MAX_VALUE;
							System.out.println("   took: " + Time.printTime(System.currentTimeMillis() - startTime));
						}
					} else {
						gForw = Collections.min(keySet);
					}
					System.out.println("   next g value in forward direction: " + gForw);
                    long currentTotalReorderTime = getLastTotalReorderTime();
					lastForwTime = System.currentTimeMillis() - startTime;
					lastForwTime -= (currentTotalReorderTime - lastTotalReorderTime);
                    maxForwTime = Math.max(maxForwTime, lastForwTime);
					System.out.println("   took: " + Time.printTime(lastForwTime));
                    MAX_STEP_TIME = Math.max(INITIAL_MAX_STEP_TIME, (long) ((maxForwTime + getLastReorderTime()) * TIME_INCREMENT));
				}
                if (WRITING_NECESSARY) {
				try {
					FileWriter writer = new FileWriter(dijkstraDir + "gForw.txt");
					writer.write(gForw + "\n");
					writer.flush();
					writer.close();
					writer = new FileWriter(dijkstraDir + "optGForw.txt");
					writer.write(optGForw + "\n");
					writer.flush();
					writer.close();
					writer = new FileWriter(dijkstraDir + "optGBackw.txt");
					writer.write(optGBackw + "\n");
					writer.flush();
					writer.close();
					writer = new FileWriter(dijkstraDir + "optVecIndexForw.txt");
					writer.write(optVecIndexForw + "\n");
					writer.flush();
					writer.close();
					writer = new FileWriter(dijkstraDir + "optVecIndexBackw.txt");
					writer.write(optVecIndexBackw + "\n");
					writer.flush();
					writer.close();
					writer = new FileWriter(dijkstraDir + "optCost.txt");
					writer.write(optCost + "\n");
					writer.flush();
					writer.close();
					if (optIntersection != null) {
						factory.save(dijkstraDir + "optIntersection", optIntersection);
					}
					factory.save(dijkstraDir + "closedForwTotal", closedForwTotal.get(0));
					writer = new FileWriter(dijkstraDir + "closedForw.txt", true);
					if (!closedForw.containsKey(oldG)) {
						writer.write(oldG + " -1");
					} else {
						Vector<BDD> closedToStore = closedForw.get(oldG);
						writer.write(oldG + "");
						for (int i = 0; i < closedToStore.size(); i++) {
							factory.save(dijkstraDir + "closedForw_" + oldG + "_" + i, closedToStore.get(i));
							writer.write(" " + i);
						}
					}
					writer.write("\n");
					writer.flush();
					writer.close();
					Iterator<Map.Entry<Integer, BDD>> openIt = openForw.entrySet().iterator();
					writer = new FileWriter(dijkstraDir + "openForw.txt", true);
					while (openIt.hasNext()) {
						Map.Entry<Integer, BDD> entry = openIt.next();
						if (!storedOpenForwSteps.contains(entry.getKey())) {
							writer.write(entry.getKey() + "\n");
							storedOpenForwSteps.add(entry.getKey());
						}
						factory.save(dijkstraDir + "openForw_" + entry.getKey(), entry.getValue());
					}
					writer.flush();
					writer.close();
				} catch (Exception e) {
					System.err.println("Error: " + e.getMessage());
					e.printStackTrace();
					System.exit(1);
				}
                }
			}
		}
		System.out.println("Solution found; optimal cost: " + optCost);
		Vector<BDD> vec;
		Set<Integer> keySet;
		int key;
		while (true) {
			keySet = openForw.keySet();
			if (keySet.size() == 0) {
				break;
			}
			key = Collections.min(keySet);
			if (key <= optGForw) {
				vec = new Vector<BDD>();
				vec.add(openForw.remove(key));
				closedForw.put(key, vec);
			} else {
				break;
			}
		}
		while (true) {
			keySet = openBackw.keySet();
			if (keySet.size() == 0) {
				break;
			}
			key = Collections.min(keySet);
			if (key <= optGBackw) {
				vec = new Vector<BDD>();
				vec.add(openBackw.remove(key));
				closedBackw.put(key, vec);
			} else {
				break;
			}
		}

		Iterator<BDD> valuesIt = openForw.values().iterator();
		while (valuesIt.hasNext()) {
			valuesIt.next().free();
		}
		closedForwTotal.firstElement().free();
		valuesIt = openBackw.values().iterator();
		while (valuesIt.hasNext()) {
            tmp1 = valuesIt.next();
            if (tmp1 != null)
                tmp1.free();
		}
		closedBackwTotal.firstElement().free();

		while (true) {
			keySet = closedBackw.keySet();
			key = Collections.max(keySet);
			if (key > optGBackw) {
				vec = closedBackw.remove(key);
				for (int i = 0; i < vec.size(); i++)
					vec.get(i).free();
			} else if (key == optGBackw) {
				vec = closedBackw.get(key);
				for (int i = optVecIndexBackw + 1; i < vec.size(); i++) {
					vec.get(i).free();
				}
				vec.setSize(optVecIndexBackw + 1);
				vec.lastElement().free();
				vec.set(optVecIndexBackw, optIntersection.id());
				break;
			}
		}
		while (true) {
			keySet = closedForw.keySet();
			key = Collections.max(keySet);
			if (key > optGForw) {
				vec = closedForw.remove(key);
				for (int i = 0; i < vec.size(); i++)
					vec.get(i).free();
			} else if (key == optGForw) {
				vec = closedForw.get(key);
				for (int i = optVecIndexForw + 1; i < vec.size(); i++) {
					vec.get(i).free();
				}
				vec.setSize(optVecIndexForw + 1);
				vec.lastElement().free();
				vec.set(optVecIndexForw, optIntersection);
				break;
			}
		}

		reconstructPlanDijkstra(closedForw, optGForw, closedBackw, optGBackw);

		Iterator<Vector<BDD>> closedIt = closedBackw.values().iterator();
		while (closedIt.hasNext()) {
			vec = closedIt.next();
			for (int i = 0; i < vec.size(); i++) {
                tmp1 = vec.get(i);
                if (tmp1 != null)
                    tmp1.free();
			}
		}
		closedIt = closedForw.values().iterator();
		while (closedIt.hasNext()) {
			vec = closedIt.next();
			for (int i = 0; i < vec.size(); i++) {
				vec.get(i).free();
			}
		}
		// only for debugging (finding memory leaks)...
		/*if (true) {
	    Iterator<Integer> keyIt;
	    keyIt = openForw.keySet().iterator();
	    while (keyIt.hasNext()) {
		openForw.get(keyIt.next()).free();
	    }
	    keyIt = openBackw.keySet().iterator();
	    while (keyIt.hasNext()) {
		openBackw.get(keyIt.next()).free();
	    }
	    keyIt = closedForw.keySet().iterator();
	    Vector<BDD> v;
	    while (keyIt.hasNext()) {
		v = closedForw.get(keyIt.next());
		for (int i = 0; i < v.size(); i++)
		    v.get(i).free();
	    }
	    keyIt = closedBackw.keySet().iterator();
	    while (keyIt.hasNext()) {
		v = closedBackw.get(keyIt.next());
		for (int i = 0; i < v.size(); i++)
		    v.get(i).free();
	    }
	    for (int i = 0; i < closedForwTotal.size(); i++)
		closedForwTotal.get(i).free();
	    for (int i = 0; i < closedBackwTotal.size(); i++)
		closedBackwTotal.get(i).free();
	    if (optIntersection != null)
		optIntersection.free();
	    return;
	}*/
	}

	private void reconstructPlanDijkstra(HashMap<Integer, Vector<BDD>> forwBDDs, int forwIndex, HashMap<Integer, Vector<BDD>> backwBDDs, int backwIndex) {
		LinkedList<String> solution = new LinkedList<String>();
		Vector<BDD> vec;
		int bfsIndex;
		BDD currentStates = null;
		int index = 0;

		System.out.println("   reconstructing cheapest plan ...");
		if (forwBDDs.size() > 0) {
			vec = forwBDDs.get(forwIndex);
			bfsIndex = vec.size() - 1;
			currentStates = vec.get(bfsIndex).replace(s2sp);
			reconstructPlanDijkstraOneDir(forwBDDs, forwIndex, bfsIndex, currentStates, solution, cubep, s2sp);
			currentStates = applyPlan(solution);
			index = printPlan(solution, index, true);
			solution.clear();
		}
		if (backwBDDs.size() > 0) {
			vec = backwBDDs.get(backwIndex);
			bfsIndex = vec.size() - 1;
			if (currentStates == null)
				currentStates = vec.get(bfsIndex).replace(sp2s);
			reconstructPlanDijkstraOneDir(backwBDDs, backwIndex, bfsIndex, currentStates, solution, cube, sp2s);
			printPlan(solution, index, false);
		}
		System.out.println("   done.");
	}

	private void reconstructPlanDijkstraOneDir(HashMap<Integer, Vector<BDD>> closedBDDs, int g, int bfsIndex, BDD currentStates, LinkedList<String> solution, BDDVarSet varSet, BDDPairing pairing) {
		BDD tmp1;
		BDD tmp2;
		BDD tmpStates;
		Vector<BDD> vec;
		LinkedList<BDD> actions;
		ListIterator<BDD> actionsIt;
		LinkedList<String> names;
		ListIterator<String> namesIt;

		// apply zero-cost actions
		if (bfsIndex > 0) {
			vec = closedBDDs.get(g);
			actions = t.get(0);
			names = actionNames.get(0);
			while (bfsIndex > 0) {
				bfsIndex--;
				actionsIt = actions.listIterator();
				namesIt = names.listIterator();
				while (actionsIt.hasNext()) {
					tmp1 = actionsIt.next().relprod(currentStates, varSet);
					tmp2 = tmp1.and(vec.get(bfsIndex));
					tmp1.free();
					if (!tmp2.equals(factory.zero())) {
						currentStates.free();
						currentStates = tmp2.replace(pairing);
						tmp2.free();
						solution.addFirst(namesIt.next());
						break;
					}
					namesIt.next();
				}
			}
		}

		if (g == 0) {
			currentStates.free();
			return;
		}

		// find states in some predecessor bucket
		Iterator<Integer> costsIt = actionCosts.descendingIterator();
		int cost;
		while (costsIt.hasNext()) {
			cost = costsIt.next();
			if (g - cost < 0)
				continue;
			vec = closedBDDs.get(g - cost);
			if (vec == null)
				continue;
			actions = t.get(cost);
			names = actionNames.get(cost);
			actionsIt = actions.listIterator();
			namesIt = names.listIterator();
			while (actionsIt.hasNext()) {
				tmpStates = actionsIt.next().relprod(currentStates, varSet);
				for (int vecIndex = 0; vecIndex < vec.size(); vecIndex++) {
					tmp1 = vec.get(vecIndex).and(tmpStates);
					if (!tmp1.equals(factory.zero())) {
						currentStates.free();
						currentStates = tmp1.replace(pairing);
						tmp1.free();
						tmpStates.free();
						solution.addFirst(namesIt.next());
						reconstructPlanDijkstraOneDir(closedBDDs, g - cost, vecIndex, currentStates, solution, varSet, pairing);
						return;
					}
				}
				tmpStates.free();
				namesIt.next();
			}
		}
		System.err.println("Something went wrong in the solution reconstruction.");
		System.exit(1);
	}

	private BDD applyPlan(LinkedList<String> plan) {
		BDD tmp1;
		BDD tmp2;
		BDD ret = init.id();
		String str;
		ListIterator<Integer> costIt;
		int cost = -1;
		LinkedList<String> names;
		int index;

		if (t.containsKey(0))
			actionCosts.addFirst(0);
		ListIterator<String> planIt = plan.listIterator();
		while (planIt.hasNext()) {
			str = planIt.next();
			costIt = actionCosts.listIterator();
			index = -1;
			while (index == -1) {
				cost = costIt.next();
				names = actionNames.get(cost);
				index = names.indexOf(str);
			}
			tmp1 = ret;
			tmp2 = t.get(cost).get(index).relprod(tmp1, cube);
			tmp1.free();
			ret = tmp2.replace(sp2s);
			tmp2.free();
		}
		if (t.containsKey(0))
			actionCosts.removeFirst();
		return ret;
	}

	private int printPlan(LinkedList<String> plan, int startIndex, boolean correctOrder) {
		try {
			FileWriter writer = new FileWriter("plan_output", true);
			int initialOutputCapacity = 10000;
			StringBuilder output = new StringBuilder(initialOutputCapacity);
			int counter = startIndex;
			while (!plan.isEmpty()) {
				String nextAction = "";
				if (correctOrder)
					nextAction = plan.removeFirst();
				else
					nextAction = plan.removeLast();
				String nextActionParts[] = nextAction.split("[.]");
				output.append(counter++ + ": (").append(nextActionParts[0]);
				for (int i = 1; i < nextActionParts.length; i++) {
					output.append(" ").append(nextActionParts[i]);
				}
				output.append(")\n");
				System.out.println("      (" + nextAction + ")");
				if (output.length() > initialOutputCapacity) {
					writer.write(output.toString());
					output = output.delete(0, output.length());
				}
			}
			writer.write(output.toString());
			output = output.delete(0, output.length());
			writer.close();
			return counter;
		} catch (Exception e) {
			System.err.println("Error: " + e.getMessage());
			e.printStackTrace(System.err);
			System.exit(1);
		}
		return -1;
	}

	public static <T extends Comparable<? super T>> List<T> sortCollection(
			Collection<T> c) {
		List<T> list = new ArrayList<T>(c);
		java.util.Collections.sort(list);
		return list;
	}

	public double checkBackwardVsForwardTime() {
		long startTime = System.currentTimeMillis();
		boolean backwardOK = testImage(trueGoal.id(), cubep, s2sp);
		if (!backwardOK) {
			System.out.println("backward step took too long.");
			return Double.MAX_VALUE;
		}
		long backwardTime = System.currentTimeMillis() - startTime;
		System.out.println("backward step took " + Time.printTime(backwardTime));

		startTime = System.currentTimeMillis();
		testImage(init.id(), cube, sp2s);
		long forwardTime = System.currentTimeMillis() - startTime;
		System.out.println("forward step took " + Time.printTime(forwardTime));
		if (forwardTime == 0)
			forwardTime = 1;
		return (double) backwardTime / (double) forwardTime;
	}

	private BDD costTestImage(int cost, BDD from, BDDVarSet varSet, long remainingTime) {
		return costTestImage(cost, from, factory.one(), varSet, remainingTime);
	}

	private BDD costTestImage(int cost, BDD from, BDD conjunct, BDDVarSet varSet, long remainingTime) {
		BDD tmp1;
		BDD tmp2;
		long startTime = System.currentTimeMillis();
		LinkedList<BDD> t_cost = t.get(cost);
		Vector<BDD> array = new Vector<BDD>(t_cost.size());
		for (int i = 0; i < t_cost.size(); i++) {
			tmp1 = t_cost.get(i).relprod(from, varSet);
			array.add(tmp1.and(conjunct));
			tmp1.free();
		}

		for (int i = 0; i < array.size(); i++) {
			tmp1 = array.get(i);
			i++;
			if (i < array.size()) {
				tmp2 = array.get(i);
				array.add(tmp1.or(tmp2));
				tmp1.free();
				tmp2.free();
				if (System.currentTimeMillis() - startTime > remainingTime) {
					for (int j = i + 1; j < array.size(); j++) {
						array.get(j).free();
					}
					return null;
				}
			}
		}
		return array.lastElement();
	}

	private final long MAX_TIME = 30 * 1000;

	private boolean testImage(BDD from, BDDVarSet varSet, BDDPairing pairing) {
		BDD tmp1;
		BDD tmp2;
		long startTime = System.currentTimeMillis();
		BDD reached = factory.zero();

		if (t.containsKey(0)) {
			while (true) {
				tmp1 = costTestImage(0, from, varSet, MAX_TIME - (System.currentTimeMillis() - startTime));
				from.free();
				if (tmp1 == null) {
					reached.free();
					return false;
				}
				tmp2 = tmp1.replace(pairing);
				tmp1.free();
				tmp1 = reached.not();
				from = tmp1.and(tmp2);
				tmp1.free();
				tmp2.free();
				tmp1 = reached;
				reached = tmp1.or(from);
				tmp1.free();
				if (from.equals(factory.zero()) || System.currentTimeMillis() - startTime > MAX_TIME) {
					break;
				}
			}
		} else {
			reached = from;
		}
		if (System.currentTimeMillis() - startTime > MAX_TIME) {
			reached.free();
			return false;
		}

		int c;
		ListIterator<Integer> costIt = actionCosts.listIterator();
		while (costIt.hasNext()) {
			c = costIt.next();
			tmp1 = costTestImage(c, reached, varSet, MAX_TIME - (System.currentTimeMillis() - startTime));
			if (tmp1 == null) {
				reached.free();
				return false;
			}
			tmp2 = tmp1.replace(pairing);
			tmp1.free();
			tmp2.free();
			if (System.currentTimeMillis() - startTime > MAX_TIME) {
				reached.free();
				return false;
			}
		}
		reached.free();
		return true;
	}
}
