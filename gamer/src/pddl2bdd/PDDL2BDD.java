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

package pddl2bdd;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.File;
import java.util.LinkedList;
import java.util.ListIterator;
import java.util.Vector;
import pddl2bdd.parser.GroundedPDDLParser;
import pddl2bdd.parser.logic.*;
import pddl2bdd.pddl2bdd.MakeFDD;
import pddl2bdd.pddl2bdd.MakeFDDAStar;
import pddl2bdd.pddl2bdd.MakeAbstractFDD;
import pddl2bdd.pddl2bdd.MakeFDDDijkstra;
import pddl2bdd.util.Maths;
import pddl2bdd.util.Time;
import pddl2bdd.variableOrdering.CausalGraph;
import pddl2bdd.variableOrdering.CausalGraphNode;
import pddl2bdd.variableOrdering.heuristic.*;

/**
 * This class converts the (instantiated) domain- and problem-files into BDDs.
 * 
 * @author Peter Kissmann
 * @version 2.0
 */
public class PDDL2BDD {
	public static boolean COSTS = false;
	public static boolean BIDIRECTIONAL = true;
	public static boolean BFS = false;
	public static boolean ASTAR = true;
	public static boolean DIJKSTRA = false;
	public static boolean ABSTRACT = false;
	public static boolean USENOMOREABSTRACTION = true;
	public static boolean USEBETTERVARIABLEORDERING = true;
	public static boolean USEABSTRACTION = true;
	public static boolean AUTOMATEDBIDIR = true;
	public static orderings ORDERING = orderings.gamer00;
    public static double REORDERING_TIME = 0.0;
    public static int REORDERING_STEPS = 0;

	public enum orderings {
		butler,
		cg,
		cgbfs,
		cgbfs_single,
		chung1,
		chung2,
		gamer00,
		gamer01,
		gamer10,
		gamer11,
		greedy,
		malik,
		minato,
		random,
		weightedgamer00,
		weightedgamer01,
		weightedgamer10,
		weightedgamer11
	}

	public static void printCall() {
		System.err.println("Error in program call!");
		System.err
		.println("call: java -classpath <path to gamer.jar>:<path to JavaBDD jar> -Dbdd=<BDD package> <name of problem file> <BDD package> [options]");
		System.err.println("possible options:");
		System.err
		.println("\t-a (--astar): use of A* search, if only uniform costs present (default: uses BFS)");
		System.err
		.println("\t-d (--dijkstra): use of Dijkstra search instead of A* search (default: uses BFS or A*)");
		System.err
		.println("\t-u (--unidir): use unidirectional search in case of BFS or Dijkstra search (default: uses bidirectional search)");
		System.err
		.println("\t-p (--partial-pdb): use no heuristic in case of A* search (default: builds a pattern database)");
		System.err
		.println("\t-s (--smaller-pdb): use smaller patterns for pattern database (default: no abstraction)");
		System.err
		.println("\t-f (--fixed-ordering): use variable ordering specified by partition file (default: calculates better ordering based on CG)");
		System.err
		.println("\t-c (--choice): use bidirectional vs. unidirectional BFS or PDB construction style as specified (default: will determine which to choose depending on expansion times for first forward and backward BFS layers)");
		System.err
		.println("\t-o <type> (--ordering=<type>): use variable ordering heuristic <type>");
		System.err.println("\t\tallowed types:");
		System.err.println("\t\t\tButler");
		System.err.println("\t\t\tCG");
		System.err.println("\t\t\tCG-BFS");
		System.err.println("\t\t\tCG-BFS_Single");
		System.err.println("\t\t\tChung1");
		System.err.println("\t\t\tChung2");
		System.err.println("\t\t\tGamer");
		System.err.println("\t\t\tGamerInv");
		System.err.println("\t\t\tGamerBidir");
		System.err.println("\t\t\tGamerBidirInv");
		System.err.println("\t\t\tGreedy");
		System.err.println("\t\t\tMalik");
		System.err.println("\t\t\tMinato");
		System.err.println("\t\t\tRandom");
		System.err.println("\t\t\tWeightedGamer");
		System.err.println("\t\t\tWeightedGamerInv");
		System.err.println("\t\t\tWeightedGamerBidir");
		System.err.println("\t\t\tWeightedGamerBidirInv");
        System.err
        .println("\t-r <time (double)> (--reordering-time=<time (double)>): use automatical reordering for up to <time> seconds");
        System.err.println("\t-n <num> (--num-reorderings=<num>): use up to <num> reorderings; if <num>=-1, no limit is set (i.e., infinity)");
        /*System.err.println("\t-i <type> (--criterion=<type>): stop automatic reordering based on criterion <type>");
        System.err.println("\t\tallowed types:");
        System.err.println("\t\t\tpercentage");
        System.err.println("\t\t\tfactor <factor (double)>");
        System.err.println("\t\t\tboth <factor (double)>");*/
		System.exit(1);
	}

	/**
	 * The main method that performs the conversion.
	 * 
	 * @param args
	 *            Contains all the parameters of the program call.
	 */
	public static void main(String[] args) {
		MakeFDD maker = null;
		MakeFDDAStar makerA = null;
		MakeAbstractFDD absMaker = null;
		MakeFDDDijkstra makerD = null;
		long startingTime;
		long endingTime = 0;
		String partFileName;
		String bddLibrary;
		boolean useAstarAnyway = false;
		boolean useDijkstra = false;

        /*try {
            File exec = new File(PDDL2BDD.class.getProtectionDomain().getCodeSource().getLocation().toURI());
            String location = exec.toString();
            String[] locationParts = location.split("/");
            String[] dirParts = locationParts[locationParts.length - 3].split("_");
            REORDERING_TIME = Double.parseDouble(dirParts[dirParts.length - 1]);
            System.out.println("allowed reordering time: " + REORDERING_TIME);
        } catch (Exception e) {
        }*/
        /*try {
            File exec = new File(PDDL2BDD.class.getProtectionDomain().getCodeSource().getLocation().toURI());
            String location = exec.toString();
            String[] locationParts = location.split("/");
            String[] dirParts = locationParts[locationParts.length - 3].split("_");
            REORDERING_STEPS = Integer.parseInt(dirParts[dirParts.length - 1]);
            System.out.println("allowed reordering steps: " + REORDERING_STEPS);
        } catch (Exception e) {
        }*/

		if (args.length < 2) {
			System.err.println("Error: not enough arguments in program call!");
			printCall();
		}
		partFileName = args[0];
		bddLibrary = args[1];
		for (int i = 2; i < args.length; i++) {
			if (args[i].equals("-a") || args[i].equals("--astar"))
				useAstarAnyway = true;
			else if (args[i].equals("-u") || args[i].equals("--unidir"))
				BIDIRECTIONAL = false;
			else if (args[i].equals("-d") || args[i].equals("--dijkstra"))
				useDijkstra = true;
			else if (args[i].equals("-p") || args[i].equals("--partial-pdb"))
				USEABSTRACTION = false;
			else if (args[i].equals("-s") || args[i].equals("--smaller-pdb"))
				USENOMOREABSTRACTION = false;
			else if (args[i].equals("-f") || args[i].equals("--fixed-ordering"))
				USEBETTERVARIABLEORDERING = false;
			else if (args[i].equals("-c") || args[i].equals("--choice"))
				AUTOMATEDBIDIR = false;
			else if (args[i].equals("-o") || args[i].startsWith("--ordering=")) {
				if (args[i].equals("-o"))
					i++;
				else
					args[i] = args[i].substring(11);
				if (args[i].equalsIgnoreCase("butler")) {
					ORDERING = orderings.butler;
				} else if (args[i].equalsIgnoreCase("cg")) {
					ORDERING = orderings.cg;
				} else if (args[i].equalsIgnoreCase("cg-bfs")) {
					ORDERING = orderings.cgbfs;
				} else if (args[i].equalsIgnoreCase("cg-bfs_single")) {
					ORDERING = orderings.cgbfs_single;
				} else if (args[i].equalsIgnoreCase("chung1")) {
					ORDERING = orderings.chung1;
				} else if (args[i].equalsIgnoreCase("chung2")) {
					ORDERING = orderings.chung2;
				} else if (args[i].equalsIgnoreCase("gamer")) {
					ORDERING = orderings.gamer00;
				} else if (args[i].equalsIgnoreCase("gamerInv")) {
					ORDERING = orderings.gamer01;
				} else if (args[i].equalsIgnoreCase("gamerBidir")) {
					ORDERING = orderings.gamer10;
				} else if (args[i].equalsIgnoreCase("gamerBidirInv")) {
					ORDERING = orderings.gamer11;
				} else if (args[i].equalsIgnoreCase("greedy")) {
					ORDERING = orderings.greedy;
				} else if (args[i].equalsIgnoreCase("malik")) {
					ORDERING = orderings.malik;
				} else if (args[i].equalsIgnoreCase("minato")) {
					ORDERING = orderings.minato;
				} else if (args[i].equalsIgnoreCase("random")) {
					ORDERING = orderings.random;
				} else if (args[i].equalsIgnoreCase("weightedGamer")) {
					ORDERING = orderings.weightedgamer00;
				} else if (args[i].equalsIgnoreCase("weightedGamerInv")) {
					ORDERING = orderings.weightedgamer01;
				} else if (args[i].equalsIgnoreCase("weightedGamerBidir")) {
					ORDERING = orderings.weightedgamer10;
				} else if (args[i].equalsIgnoreCase("weightedGamerBidirInv")) {
					ORDERING = orderings.weightedgamer11;
				} else {
					System.err.println("Error: unknown ordering heuristic " + args[i] + " in program call!");
					printCall();
				}
			} else if (args[i].equals("-r") || args[i].startsWith("--reordering-time=")) {
                if (args[i].equals("-o"))
                    i++;
                else
                    args[i] = args[i].substring(18);
			    REORDERING_TIME = Double.parseDouble(args[i]);
            } else if (args[i].equals("-n") || args[i].startsWith("--num-reorderings=")) {
                if (args[i].equals("-n"))
                    i++;
                else
                    args[i] = args[i].substring(18);
                REORDERING_STEPS = Integer.parseInt(args[i]);
                if (REORDERING_STEPS < 0) {
                    REORDERING_STEPS = Integer.MAX_VALUE;
                }
            /*} else if (args[i].equals("-i") || args[i].startsWith("--criterion=")) {
                if (args[i].equals("-i"))
                    i++;
                else
                    args[i] = args[i].substring(12);
                if (args[i].equalsIgnoreCase("percentage")) {
                    
                } else if (args[i].equalsIgnoreCase("factor")) {
                    
                } else if (args[i].equalsIgnoreCase("both")) {
                    
                } else {
                    System.err.println("Error: unknown criterion for stopping automatic reordering " + args[i] + " in program call!");
                    printCall();
                }*/
			} else {
				System.err.println("Error: unknown argument " + args[i]
						+ " in program call!");
				printCall();
			}
		}

		startingTime = System.currentTimeMillis();

		// delete derived predicates
		GroundedPDDLParser.parse(partFileName);
		COSTS = !GroundedPDDLParser.isUniformCost();
		if (useAstarAnyway)
			COSTS = true;
		BFS = !COSTS;
		if (useDijkstra) {
			ASTAR = false;
			DIJKSTRA = COSTS;
		} else {
			ASTAR = COSTS;
			DIJKSTRA = false;
		}
		endingTime = System.currentTimeMillis();
		System.out.println("parsing took "
				+ Time.printTime(endingTime - startingTime));

		// transform into BDD
		if (partFileName.startsWith("abstract")) {
			ABSTRACT = true;
		}
		LinkedList<Integer> emptyPartitions = new LinkedList<Integer>();
		if ((ABSTRACT && BFS) || (ABSTRACT && DIJKSTRA)) {
			System.out.println("Stopping due to abstract but BFS or Dijkstra to perform!");
			System.out
			.println("Total time: "
					+ Time.printTime(System.currentTimeMillis()
							- startingTime));
			System.exit(0);
		}
		int numberOfVariables = 0;
		LinkedList<LinkedList<String>> partitions = new LinkedList<LinkedList<String>>();
		ListIterator<Vector<Predicate>> partitionIt = GroundedPDDLParser.partitioning
				.listIterator();
		while (partitionIt.hasNext()) {
			Vector<Predicate> group = partitionIt.next();
			ListIterator<Predicate> groupIt = group.listIterator();
			LinkedList<String> partition = new LinkedList<String>();
			while (groupIt.hasNext()) {
				partition.add(groupIt.next().getName());
			}
			partitions.add(partition);
			numberOfVariables += Maths.log2(group.size());
		}
		numberOfVariables = numberOfVariables * 2;
		boolean[][] influences = new boolean[GroundedPDDLParser.partitioning
		                                     .size()][GroundedPDDLParser.partitioning.size()];
		CausalGraph cg = new CausalGraph(partitions, false, true);
		for (int i = 0; i < influences.length; i++) {
			CausalGraphNode node = cg.getVariable(i);
			CausalGraphNode succ;
			for (int j = 0; j < node.getNumberOfSuccessors(); j++) {
				succ = node.getSuccessor(j);
				influences[i][succ.getVariable()] = true;
				influences[succ.getVariable()][i] = true;
			}
		}
		int[] variableOrdering;
		if (USEBETTERVARIABLEORDERING) {
			if (ASTAR && !ABSTRACT) {
				LinkedList<Integer> ordering = new LinkedList<Integer>();
				boolean useDefaultOrdering = false;
				try {
					BufferedReader bufferedReader = new BufferedReader(
							new FileReader("variableOrdering.txt"));
					String line;
					while ((line = bufferedReader.readLine()) != null) {
						ordering.add(Integer.parseInt(line));
					}
					bufferedReader.close();
				} catch (Exception e) {
					System.err.println("Warning: " + e.getMessage());
					e.printStackTrace();
					System.err.println("using default ordering");
					useDefaultOrdering = true;
				}
				variableOrdering = new int[influences.length];
				if (!useDefaultOrdering) {
					LinkedList<LinkedList<String>> newPartitions = new LinkedList<LinkedList<String>>();
					ListIterator<Integer> orderIt = ordering.listIterator();
					int index = 0;
					int nextOrderingItem;
					while (orderIt.hasNext()) {
						nextOrderingItem = orderIt.next();
						newPartitions.add(partitions.get(nextOrderingItem));
						variableOrdering[index] = nextOrderingItem;
					}
					partitions = newPartitions;
				} else {
					for (int i = 0; i < variableOrdering.length; i++) {
						variableOrdering[i] = i;
					}
				}
			} else {
				VariableOrderingHeuristic vo;
				switch (ORDERING) {
				case butler:
					vo = new Butler();
					break;
				case cg:
					vo = new CG();
					break;
				case cgbfs:
					vo = new CG(true);
					break;
				case cgbfs_single:
					vo = new CG(true, true);
					break;
				case chung1:
					vo = new Chung1();
					break;
				case chung2:
					vo = new Chung2();
					break;
				case gamer00:
					vo = new Gamer(false, false);
					break;
				case gamer01:
					vo = new Gamer(false, true);
					break;
				case gamer10:
					vo = new Gamer(true, false);
					break;
				case gamer11:
					vo = new Gamer(true, true);
					break;
				case greedy:
					vo = new Greedy();
					break;
				case malik:
					vo = new Malik();
					break;
				case minato:
					vo = new Minato();
					break;
				case random:
					vo = new Rand();
					break;
				case weightedgamer00:
					vo = new WeightedGamer(false, false);
					break;
				case weightedgamer01:
					vo = new WeightedGamer(false, true);
					break;
				case weightedgamer10:
					vo = new WeightedGamer(true, false);
					break;
				case weightedgamer11:
					vo = new WeightedGamer(true, true);
					break;
				default:
					vo = new Gamer();
					break;
				}
				variableOrdering = vo.findVariableOrdering(partitions);
				vo = null;
				try {
					FileWriter ordering = new FileWriter(
							"variableOrdering_tmp.txt");
					for (int i = 0; i < variableOrdering.length; i++) {
						ordering.write(variableOrdering[i] + "\n");
					}
					ordering.flush();
					ordering.close();
					Runtime.getRuntime().exec(
							"mv variableOrdering_tmp.txt variableOrdering.txt");
				} catch (Exception e) {
					System.err.println("Error: " + e.getMessage());
					e.printStackTrace();
					System.exit(1);
				}
				LinkedList<LinkedList<String>> newPartitions = new LinkedList<LinkedList<String>>();
				for (int i = 0; i < variableOrdering.length; i++) {
					newPartitions.add(partitions.get(variableOrdering[i]));
				}
				partitions = newPartitions;
			}
		} else {
			variableOrdering = new int[partitions.size()];
			for (int i = 0; i < variableOrdering.length; i++) {
				variableOrdering[i] = i;
			}
		}

		if (AUTOMATEDBIDIR) {
			if ((USEABSTRACTION && ABSTRACT && USENOMOREABSTRACTION)
					|| (BFS && BIDIRECTIONAL)) {
				if (COSTS) {
					endingTime = System.currentTimeMillis();
					System.out.println("Initializing planner after "
							+ Time.printTime(endingTime - startingTime));
					makerD = new MakeFDDDijkstra(partitions, numberOfVariables, bddLibrary);
					System.out.println("Initialization done; took: "
							+ Time.printTime(System.currentTimeMillis()
									- endingTime));
					endingTime = System.currentTimeMillis();
					System.out
					.println("checking time for first backward step vs. time for first forward step ...");
					double factor = makerD.checkBackwardVsForwardTime();
					if (!DIJKSTRA) {
						makerD.cleanup();
						makerD = null;
					}
					System.out.println("   result: " + factor);
					if (ASTAR && factor > 25.0) {
						System.out.println("   too long for no abstraction");
						USENOMOREABSTRACTION = false;
					}
					if (DIJKSTRA && factor == Double.MAX_VALUE) {
						System.out.println("   too long for backward Dijkstra");
						BIDIRECTIONAL = false;
					}
					System.out.println("done.");
					System.out.println("took: "
							+ Time.printTime(System.currentTimeMillis()
									- endingTime));
				} else {
					endingTime = System.currentTimeMillis();
					System.out.println("Initializing planner after "
							+ Time.printTime(endingTime - startingTime));
					maker = new MakeFDD(partitions, numberOfVariables, bddLibrary);
					System.out.println("Initialization done; took: "
							+ Time.printTime(System.currentTimeMillis()
									- endingTime));
					endingTime = System.currentTimeMillis();
					System.out
					.println("checking time for first backward step vs. time for first forward step ...");
					double factor = maker.checkBackwardVsForwardTime();
					System.out.println("   result: " + factor);
					if (factor == Double.MAX_VALUE) {
						System.out.println("   too long for backward BFS");
						BIDIRECTIONAL = false;
					}
					System.out.println("done.");
					System.out.println("took: "
							+ Time.printTime(System.currentTimeMillis()
									- endingTime));
				}
			}
		}

		endingTime = System.currentTimeMillis();
		System.out.println("Total time so far: "
				+ Time.printTime(endingTime - startingTime));
		System.out.println("creating BDD ...");
		if (ABSTRACT) {
			if (USEABSTRACTION) {
				if (USENOMOREABSTRACTION) {
					try {
						File usedPDBsFile = new File("usePDBs.txt");
						FileWriter usePDBs = new FileWriter("usePDBs_tmp.txt");
						if (usedPDBsFile.exists()) {
							LinkedList<String> usedPDBs = new LinkedList<String>();
							BufferedReader bufferedReader = new BufferedReader(
									new FileReader("usePDBs.txt"));
							String line;
							while ((line = bufferedReader.readLine()) != null) {
								usedPDBs.add(line);
							}
							bufferedReader.close();
							ListIterator<String> usedIt = usedPDBs
									.listIterator();
							while (usedIt.hasNext()) {
								usePDBs.write(usedIt.next() + "\n");
							}
						}
						String pdbID = partFileName.split("-", 2)[0];
						pdbID = pdbID.substring(8);
						usePDBs.write(pdbID + "\n");
						usePDBs.flush();
						usePDBs.close();
						String abstractionFileName = partFileName.substring(0,
								partFileName.length() - 8);
						FileWriter maxPDB = new FileWriter(abstractionFileName
								+ "MaxPDB.txt");
						maxPDB.write("-1\n");
						maxPDB.flush();
						maxPDB.close();
						FileWriter exPDB = new FileWriter(abstractionFileName
								+ "ExPDBs.txt");
						exPDB.write("");
						exPDB.flush();
						exPDB.close();
						Runtime.getRuntime().exec(
								"mv usePDBs_tmp.txt usePDBs.txt");
					} catch (Exception e) {
						System.err.println("Error: " + e.getMessage());
						e.printStackTrace();
						System.exit(1);
					}
					absMaker = new MakeAbstractFDD(partitions, emptyPartitions,
							numberOfVariables, bddLibrary, partFileName);
					System.out.println("building PDB ...");
					long time1 = System.currentTimeMillis();
					if (partFileName.startsWith("super-abstract"))
						absMaker.buildSuperPDB();
					else
						absMaker.buildPDB(false);
					long time2 = System.currentTimeMillis();
					System.out.println("done.");
					System.out.println("construction time: "
							+ Time.printTime(time2 - time1));
					System.out.println("cleaning up ...");
					absMaker.cleanup();
					System.out.println("done.");
				} else {
					LinkedList<Integer> chosenPartitions = new LinkedList<Integer>();
					Vector<Predicate> allPreds = new Vector<Predicate>();
					GroundedPDDLParser.goalDescription.getAllPredicates(allPreds);
					Vector<String> goalTokens = new Vector<String>(allPreds.size());
					ListIterator<Predicate> predIt = allPreds.listIterator();
					while (predIt.hasNext()) {
						goalTokens.add(predIt.next().getName());
					}
					ListIterator<LinkedList<String>> partIt = partitions.listIterator();
					LinkedList<String> group;
					int index = 0;
					index = 0;
					while (partIt.hasNext()) {
						boolean foundElement = false;
						group = partIt.next();
						for (int i = 0; i < goalTokens.size(); i++) {
							if (group.contains(goalTokens.elementAt(i))) {
								foundElement = true;
								break;
							}
						}
						if (foundElement) {
							chosenPartitions.add(index);
						} else {
							emptyPartitions.add(index);
						}
						index++;
					}
					int bestIndex = 1;
					double bestAverage = -1;
					int additional;
					double[] averages;
					try {
						FileWriter maxPDB = new FileWriter(
								"abstract1-1MaxPDB.txt");
						maxPDB.write("-1\n");
						maxPDB.flush();
						maxPDB.close();
						FileWriter exPDB = new FileWriter(
								"abstract1-1ExPDBs.txt");
						exPDB.write("");
						exPDB.flush();
						exPDB.close();
						FileWriter usePDBs = new FileWriter("usePDBs_tmp.txt");
						usePDBs.write("1\n");
						usePDBs.flush();
						usePDBs.close();
						Runtime.getRuntime().exec(
								"mv usePDBs_tmp.txt usePDBs.txt");
					} catch (Exception e) {
						System.err.println("Error: " + e.getMessage());
						e.printStackTrace();
						System.exit(1);
					}
					String partitionFileName = new String("abstract1-1Part.gdl");
					endingTime = System.currentTimeMillis();
					absMaker = new MakeAbstractFDD(partitions, emptyPartitions,
							numberOfVariables, bddLibrary, partitionFileName);
					System.out.println("Initialization took "
							+ Time.printTime(System.currentTimeMillis()
									- endingTime));
					System.out.println("building PDB ...");
					long time1 = System.currentTimeMillis();
					if (partFileName.startsWith("super-abstract"))
						absMaker.buildSuperPDB();
					else
						bestAverage = absMaker.buildPDB(true);
					long time2 = System.currentTimeMillis();
					System.out.println("done.");
					System.out.println("construction time: "
							+ Time.printTime(time2 - time1));
					System.out.println("cleaning up ...");
					absMaker.cleanup();
					System.out.println("done.");
					while (bestIndex != -1) {
						additional = bestIndex + 1;
						bestIndex = -1;
						averages = new double[emptyPartitions.size()];
						for (index = 0; index < emptyPartitions.size(); index++) {
							boolean isInfluencing = false;
							System.out.println("index: " + index);
							int oldEmptyPartition = emptyPartitions.get(index);
							ListIterator<Integer> chosenIt = chosenPartitions
									.listIterator();
							while (chosenIt.hasNext()) {
								if (influences[variableOrdering[oldEmptyPartition]][variableOrdering[chosenIt
								                                                                     .next()]]) {
									isInfluencing = true;
									break;
								}
							}
							if (!isInfluencing)
								continue;
							emptyPartitions.remove(index);
							partitionFileName = new String("abstract"
									+ (index + additional) + "-1Part.gdl");
							endingTime = System.currentTimeMillis();
							absMaker = new MakeAbstractFDD(partitions,
									emptyPartitions, numberOfVariables,
									bddLibrary, partitionFileName);
							System.out.println("Initialization took "
									+ Time.printTime(System.currentTimeMillis()
											- endingTime));
							System.out.println("building PDB ...");
							time1 = System.currentTimeMillis();
							if (partFileName.startsWith("super-abstract"))
								absMaker.buildSuperPDB();
							else
								averages[index] = absMaker.buildPDB(true);
							if (averages[index] > bestAverage) {
								bestAverage = averages[index];
								bestIndex = index + additional;
								try {
									FileWriter usePDBs = new FileWriter(
											"usePDBs_tmp.txt");
									usePDBs.write(bestIndex + "\n");
									usePDBs.flush();
									usePDBs.close();
									Runtime.getRuntime().exec(
											"mv usePDBs_tmp.txt usePDBs.txt");
								} catch (Exception e) {
									System.err.println("Error: "
											+ e.getMessage());
									e.printStackTrace();
									System.exit(1);
								}
							}
							time2 = System.currentTimeMillis();
							System.out.println("done.");
							System.out.println("construction time: "
									+ Time.printTime(time2 - time1));
							System.out.println("cleaning up ...");
							absMaker.cleanup();
							System.out.println("done.");
							emptyPartitions.add(index, oldEmptyPartition);
						}
						System.out.println("best index: " + bestIndex
								+ "; best average: " + bestAverage);
						if (bestIndex != -1) {
							int numberAdded = 0;
							for (int i = emptyPartitions.size() - 1; i >= 0; i--) {
								if (averages[i] >= 0.999 * bestAverage) {
									System.out.println("also chosen index: "
											+ (i + additional) + "; average: "
											+ averages[i]);
									chosenPartitions.add(emptyPartitions
											.remove(i));
									numberAdded++;
								}
							}
							if (numberAdded > 1) {
								// if adding more than one group, the new PDB
								// will be generated, as it might contain all
								// groups and would not be generated otherwise
								partitionFileName = new String("abstract"
										+ (bestIndex + 1) + "-1Part.gdl");
								absMaker = new MakeAbstractFDD(partitions,
										emptyPartitions, numberOfVariables,
										bddLibrary, partitionFileName);
								System.out.println("building new PDB ...");
								time1 = System.currentTimeMillis();
								if (partFileName.startsWith("super-abstract"))
									absMaker.buildSuperPDB();
								else {
									averages[0] = absMaker.buildPDB(true);
									System.out.println("average: "
											+ averages[0]);
									if (averages[0] > bestAverage) {
										bestAverage = averages[0];
										bestIndex = bestIndex + 1;
										try {
											FileWriter usePDBs = new FileWriter(
													"usePDBs_tmp.txt");
											usePDBs.write(bestIndex + "\n");
											usePDBs.flush();
											usePDBs.close();
											Runtime
											.getRuntime()
											.exec(
													"mv usePDBs_tmp.txt usePDBs.txt");
										} catch (Exception e) {
											System.err.println("Error: "
													+ e.getMessage());
											e.printStackTrace();
											System.exit(1);
										}
									}
								}
								time2 = System.currentTimeMillis();
								System.out.println("done.");
								System.out.println("construction time: "
										+ Time.printTime(time2 - time1));
								System.out.println("cleaning up ...");
								absMaker.cleanup();
								System.out.println("done.");
							}
						}
					}
					System.out.println("done.");
				}
			}
		} else if (BFS) {
			if (maker == null) {
				maker = new MakeFDD(partitions, numberOfVariables, bddLibrary);
				System.out.println("Initialization took: "
						+ Time.printTime(System.currentTimeMillis()
								- endingTime));
				System.out.println("done.");
			}
			GroundedPDDLParser.cleanup();
			System.out.println("finding shortest plan ...");
			endingTime = System.currentTimeMillis();
			maker.findPlanBFS(BIDIRECTIONAL);
			System.out.println("done.");
			System.out.println("took: "
					+ Time.printTime(System.currentTimeMillis() - endingTime));
			//System.out.println("cleaning up ...");
			//maker.cleanup();
            System.out.println("peak nodecount: " + maker.factory.getNodeTableSize());
            maker.factory.done();
			//System.out.println("done.");
		} else if (ASTAR) {
			makerA = new MakeFDDAStar(partitions, numberOfVariables,
					bddLibrary, partFileName);
			System.out.println("Initialization took: "
					+ Time.printTime(System.currentTimeMillis() - endingTime));
			System.out.println("done.");
			GroundedPDDLParser.cleanup();
			System.out.println("finding cheapest plan ...");
			long time1 = System.currentTimeMillis();
			// makerA.findPlanAStar();
			makerA.findPlanAStarNew();
			long time2 = System.currentTimeMillis();
			System.out.println("done.");
			System.out.println("A* search time: "
					+ Time.printTime(time2 - time1));
			//System.out.println("cleaning up ...");
			//makerA.cleanup();
            System.out.println("peak nodecount: " + makerA.factory.getNodeTableSize());
            makerA.factory.done();
			//System.out.println("done.");
		} else if (DIJKSTRA) {
			if (makerD == null) {
				makerD = new MakeFDDDijkstra(partitions, numberOfVariables, bddLibrary);
				System.out.println("Initialization took: "
						+ Time.printTime(System.currentTimeMillis() - endingTime));
				System.out.println("done.");
			}
			GroundedPDDLParser.cleanup();
			System.out.println("finding cheapest plan ...");
			long time1 = System.currentTimeMillis();
			makerD.findPlanDijkstra(BIDIRECTIONAL);
			long time2 = System.currentTimeMillis();
			System.out.println("done.");
			System.out.println("Dijkstra search time: "
					+ Time.printTime(time2 - time1));
			//System.out.println("cleaning up ...");
			//makerD.cleanup();
            System.out.println("peak nodecount: " + makerD.factory.getNodeTableSize());
            makerD.factory.done();
			//System.out.println("done.");
		}

		endingTime = System.currentTimeMillis() - startingTime;
		System.out.println("\ntotal time: " + Time.printTime(endingTime));
	}
}
