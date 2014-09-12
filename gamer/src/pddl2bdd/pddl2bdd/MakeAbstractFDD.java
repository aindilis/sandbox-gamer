/*
 * Gamer, a tool for finding optimal plans
 * Copyright (C) 20072012 by Peter Kissmann
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
 * This class not only creates the BDDs but also allows creation of symbolic
 * pattern databases.
 * 
 * @author Peter Kissmann
 * @version 1.7
 */
public class MakeAbstractFDD {
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
    private HashMap<Integer, LinkedList<BDD>> t; // transition relation
                                                 // (actions)
    private BDD trueGoal; // bdd representing the true (i.e. not simplified)
                          // goal-state
    private LinkedList<LinkedList<String>> partitionedVariables; // partition of
                                                                 // the boolean
                                                                 // variables as
                                                                 // given by the
                                                                 // user
    private LinkedList<String> nAryVariables; // list of all n-ary variables
    private LinkedList<BDD> nAryVariablesPreBDDs; // bdds representing the n-ary
                                                  // variables for the current
                                                  // state
    private LinkedList<BDD> nAryVariablesEffBDDs; // bdds representing the n-ary
                                                  // variables for the next
                                                  // state
    private HashMap<Integer, LinkedList<String>> actionNames; // list of all
                                                              // possible
                                                              // actions (resp.
                                                              // their names)
    private LinkedList<Integer> actionCosts;

    private int maxCost; // maximal action-cost
    private String partitionFileName;
    private LinkedList<BDD> superPDB;
    private int superPDBSize = 0;
    private BDDVarSet abstractedPreVars;
    private boolean[] unusedVarIndices;

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
     * @param emptyPartitions
     *            The list of abstracted variables.
     * @param numberOfVars
     *            The number of boolean variables to be used (equals twice the
     *            number of boolean variables needed for one state).
     * @param library
     *            The BDD library used.
     * @param partitionFileName
     *            name of the corresponding partition's file. This is needed to
     *            calculate the name for the PDB-files.
     */
    public MakeAbstractFDD(LinkedList<LinkedList<String>> partitions,
            LinkedList<Integer> emptyPartitions, int numberOfVars,
            String library, String partitionFileName) {
        File goalFile = new File("goal");
        if (goalFile.exists()) {
            System.out.println("goal exists");
        } else {
            System.out.println("goal not present");
        }
        this.numberOfVariables = numberOfVars;
        this.partitionedVariables = partitions;
        this.partitionFileName = partitionFileName;

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
        partIt = partitions.listIterator();
        unusedVarIndices = new boolean[arraySize];
        ListIterator<Integer> emptyIt = emptyPartitions.listIterator();
        int index = 0;
        int maxIndex = 0;
        while (emptyIt.hasNext()) {
            int foundIndex = emptyIt.next();
            while (index < foundIndex) {
                maxIndex += partIt.next().size();
                index++;
            }
            int size = partIt.next().size();
            for (int i = maxIndex; i < maxIndex + size; i++)
                unusedVarIndices[i] = true;
            maxIndex += size;
            index++;
        }

        // build the transition relation
        System.out.println("   building transition relation ...");
        actionNames = new HashMap<Integer, LinkedList<String>>();
        t = new HashMap<Integer, LinkedList<BDD>>();
        actionCosts = new LinkedList<Integer>();
        maxCost = -1;
        ListIterator<Action> actionIt = GroundedPDDLParser.actions
                .listIterator();
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
        boolean[] usedActions = new boolean[GroundedPDDLParser.actions.size()];
        int usedActionIndex = 0;
        actionIt = GroundedPDDLParser.actions.listIterator();
        while (actionIt.hasNext()) {
            Action action = actionIt.next();
            BDD actionBDD = action.createBDD(factory, nAryVariables,
                    nAryVariablesPreBDDs, nAryVariablesEffBDDs, partitions,
                    variables, unusedVarIndices);
            if (actionBDD == null) {
                action.setUnused(true);
            } else {
                usedActions[usedActionIndex] = true;
                t.get(action.getCost()).addLast(actionBDD);
                actionNames.get(action.getCost()).addLast(action.getName());
            }
            usedActionIndex++;
        }
        Set<Map.Entry<Integer, LinkedList<BDD>>> allActions = t.entrySet();
        Iterator<Map.Entry<Integer, LinkedList<BDD>>> allActionsIt = allActions
                .iterator();
        while (allActionsIt.hasNext()) {
            Map.Entry<Integer, LinkedList<BDD>> actionsEntry = allActionsIt
                    .next();
            if (actionsEntry.getValue().size() == 0) {
                actionNames.remove(actionsEntry.getKey());
                actionCosts.remove(actionsEntry.getKey());
                allActionsIt.remove();
            }
        }

        FileWriter usedActionsWriter = null;
        try {
            usedActionsWriter = new FileWriter(partitionFileName.substring(0,
                    partitionFileName.lastIndexOf(".") - 4)
                    + "UsedActions.txt");
            for (int i = 0; i < usedActions.length; i++) {
                usedActionsWriter.append(usedActions[i] ? "1" : "0");
            }
            usedActionsWriter.append("\n");
            usedActionsWriter.flush();
            usedActionsWriter.close();
        } catch (Exception e) {
            System.err.println("Error: " + e.getMessage());
            e.printStackTrace();
        }
        System.out.println("   done.");

        // build initial state
        System.out.println("   building initial state ...");
        initialize(emptyPartitions);
        System.out.println("   done.");

        // build the goal
        System.out.println("   building goal states ...");
        trueGoal = GroundedPDDLParser.goalDescription.createBDD(factory,
                                                                nAryVariables, nAryVariablesPreBDDs, nAryVariablesEffBDDs, false, unusedVarIndices);
        System.out.println("   done.");

        // read super-database
        if (partitionFileName.startsWith("abstract")) {
            int currentVar = 0;
            int[] abstractedVars = new int[numberOfVariables / 2];
            int abstractedVarsCounter = 0;
            for (int i = 0; i < partitions.size(); i++) {
                int numVars = Maths.log2(partitions.get(i).size());
                if (emptyPartitions.contains(i)) {
                    for (int j = 0; j < numVars; j++) {
                        abstractedVars[abstractedVarsCounter] = (currentVar + j) * 2;
                        abstractedVarsCounter++;
                    }
                }
                currentVar += numVars;
            }
            int[] abstractedVars2 = new int[abstractedVarsCounter];
            for (int i = 0; i < abstractedVarsCounter; i++) {
                abstractedVars2[i] = abstractedVars[i];
            }
            abstractedPreVars = factory.makeSet(abstractedVars2);

            String pdbFileNameMiddle = partitionFileName.substring(
                    partitionFileName.indexOf("-"), partitionFileName
                            .lastIndexOf(".") - 4)
                    + "PDB_";
            File file;
            String filename;
            int pdbSize = 0;
            superPDB = new LinkedList<BDD>();
            filename = "super-abstract" + pdbFileNameMiddle + "0";
            file = new File(filename);
            if (file.exists()) {
                System.out.println("   reading super-database ...");
                BDD tmp1;
                BDD tmp2;
                try {
                    System.out.println("reading file " + pdbSize);
                    tmp1 = factory.load(filename);
                    tmp2 = tmp1.exist(abstractedPreVars);
                    tmp1.free();
                    superPDB.add(tmp2.replace(s2sp));
                    tmp2.free();
                } catch (Exception e) {
                    System.err.println("Error: " + e.getMessage());
                    System.exit(1);
                }
                pdbSize++;
                while (true) {
                    filename = "super-abstract" + pdbFileNameMiddle + pdbSize;
                    file = new File(filename);
                    if (file.exists()) {
                        try {
                            System.out.println("reading file " + pdbSize);
                            tmp1 = factory.load(filename);
                            tmp2 = tmp1.exist(abstractedPreVars);
                            tmp1.free();
                            superPDB.add(tmp2.replace(s2sp));
                            tmp2.free();
                        } catch (Exception e) {
                            System.err.println("Error: " + e.getMessage());
                            System.exit(1);
                        }
                        pdbSize++;
                    } else {
                        if (superPDB.getLast().equals(factory.zero()))
                            superPDB.removeLast();
                        break;
                    }
                }
                superPDBSize = superPDB.size();
                System.out.println("   done.");
            }
        }

        if (emptyPartitions.size() == 0) {
            // write transition relation to disk
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

    private void initialize(LinkedList<Integer> emptyPartitions) {
        LinkedList<String> initialVariables;
        BDD tmp;

        init = factory.one();
        initialVariables = new LinkedList<String>();
        ListIterator<Predicate> initIt = GroundedPDDLParser.initialState
                .listIterator();
        while (initIt.hasNext()) {
            Predicate pred = initIt.next();
            String name = pred.getName();
            int index = nAryVariables.indexOf(name);
            if (unusedVarIndices[index])
                continue;
            initialVariables.add(name);
            tmp = init;
            init = nAryVariablesPreBDDs.get(index).and(init);
            tmp.free();
        }
        for (int i = 0; i < partitionedVariables.size(); i++) {
            if (emptyPartitions.contains(i))
                continue;
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
        factory.done();
    }

    private BDD image(int index, BDD from, BDDVarSet varSet) {
        return image(index, from, factory.one(), varSet);
    }

    private BDD image(int index, BDD from, BDD conjunct, BDDVarSet varSet) {
        BDD tmp1;
        BDD tmp2;
        LinkedList<BDD> t_i = t.get(index);
        int size = t_i.size();
        BDD[] array = new BDD[size];
        for (int i = 0; i < size; i++) {
            tmp1 = t_i.get(i).relprod(from, varSet);
            array[i] = tmp1.and(conjunct);
            tmp1.free();
        }

        int prevRemainingElems;
        int remainingElems = size;
        while (remainingElems > 1) {
            prevRemainingElems = remainingElems;
            remainingElems = Maths.div2(prevRemainingElems);
            for (int i = 0; i < remainingElems; i++) {
                array[i] = array[2 * i];
                if (i < remainingElems - 1 || (2 * i) + 1 < prevRemainingElems) {
                    tmp1 = array[i];
                    tmp2 = array[(2 * i) + 1];
                    array[i] = tmp1.or(tmp2);
                    tmp1.free();
                    tmp2.free();
                }
            }
        }
        return array[0];
    }

    private class DijkstraData {
        public BDD backwardReached;
        public HashMap<Integer, BDD> backwardBDDs;
    }

    private void searchStep(int index, BDDVarSet varSet, BDDPairing pairing,
            DijkstraData data) {
        BDD tmp1;
        BDD tmp2;
        BDD negatedReached;
        BDD to;
        // int currentSize;
        BDD frontier;
        BDD oldFrontier;

        negatedReached = data.backwardReached.not();
        tmp1 = data.backwardBDDs.remove(index);
        data.backwardBDDs.put(index, tmp1.and(negatedReached));
        tmp1.free();
        if (t.containsKey(0)) {
            frontier = data.backwardBDDs.get(index);
            while (!frontier.equals(factory.zero())) {
                tmp1 = image(0, frontier, varSet);
                to = tmp1.replace(pairing);
                tmp1.free();
                // oldFrontier = data.backwardBDDs.get(index);
                oldFrontier = data.backwardBDDs.remove(index);
                tmp2 = oldFrontier.not();
                frontier = to.and(tmp2);
                to.free();
                tmp2.free();
                // data.backwardBDDs.set(index, oldFrontier.or(frontier));
                data.backwardBDDs.put(index, oldFrontier.or(frontier));
                oldFrontier.free();
            }
        }
        tmp1 = data.backwardBDDs.remove(index);
        data.backwardBDDs.put(index, tmp1.and(negatedReached));
        tmp1.free();
        negatedReached.free();
        if (data.backwardReached.equals(factory.zero()))
            data.backwardReached = data.backwardBDDs.get(index).id();
        else {
            tmp1 = data.backwardReached;
            data.backwardReached = tmp1.or(data.backwardBDDs.get(index));
            tmp1.free();
        }
        negatedReached = data.backwardReached.not();
        frontier = data.backwardBDDs.get(index);
        ListIterator<Integer> costIt = actionCosts.listIterator();
        int d;
        while (costIt.hasNext()) {
            d = costIt.next();
            tmp1 = image(d, frontier, varSet);
            to = tmp1.replace(pairing);
            tmp1.free();
            tmp1 = to.and(negatedReached);
            to.free();
            to = tmp1;
            // currentSize = data.backwardBDDs.size();
            // if (currentSize <= index + maxCost) {
            // data.backwardBDDs.setSize(index + maxCost + 1);
            // for (int i = currentSize; i < index + maxCost + 1; i++)
            // data.backwardBDDs.set(i, factory.zero());
            // }
            if (!tmp1.equals(factory.zero())) {
                if (data.backwardBDDs.containsKey(index + d)) {
                    tmp1 = data.backwardBDDs.remove(index + d);
                    data.backwardBDDs.put(index + d, tmp1.or(to));
                    tmp1.free();
                    to.free();
                } else
                    data.backwardBDDs.put(index + d, to);
            }
            // tmp1 = data.backwardBDDs.get(index + d);
            // data.backwardBDDs.set(index + d, tmp1.or(to));
            // tmp1.free();
            // to.free();
        }
        negatedReached.free();
    }

    public double buildPDB(boolean calculateAverage) {
        long startingTime = System.currentTimeMillis();
        double averageHeuristic = 0.0;
        double heuristicSize = 0;
        double currentSize;
        double factor;
        double additional;
        int index;
        BDD tmp1;
        DijkstraData data = new DijkstraData();
        data.backwardBDDs = new HashMap<Integer, BDD>();
        boolean useSuperPDB = true;
        FileWriter existingPDBs = null;
        FileWriter maxPDB = null;
        try {
            existingPDBs = new FileWriter(partitionFileName.substring(0,
                    partitionFileName.lastIndexOf(".") - 4)
                    + "ExPDBs.txt");
            maxPDB = new FileWriter(partitionFileName.substring(0,
                    partitionFileName.lastIndexOf(".") - 4)
                    + "MaxPDB.txt");
        } catch (Exception e) {
            System.err.println("Error: " + e.getMessage());
            e.printStackTrace();
            System.exit(1);
        }

        index = 0;
        // data.backwardBDDs.setSize(maxCost + 1);
        data.backwardBDDs.put(index, trueGoal.id());
        // data.backwardBDDs.set(index, trueGoal.id());
        // for (int i = 1; i < maxCost + 1; i++)
        // data.backwardBDDs.set(i, factory.zero());
        data.backwardReached = factory.zero();
        // while (index < data.backwardBDDs.size()) {
        while (!data.backwardBDDs.isEmpty()) {
            index = Collections.min(data.backwardBDDs.keySet());
            System.out.println("   step: " + index);
            // if (data.backwardBDDs.get(index).equals(factory.zero())) {
            // String pdbFileName = partitionFileName.substring(0,
            // partitionFileName.lastIndexOf(".") - 4) + "PDB_";
            // try {
            // factory.save(pdbFileName + (index), factory.zero());
            // } catch (Exception e) {
            // System.err.println("Error: " + e.getMessage());
            // System.exit(1);
            // }
            try {
                maxPDB.write((index - 1) + "\n");
                maxPDB.flush();
            } catch (Exception e) {
                System.err.println("Error: " + e.getMessage());
                e.printStackTrace();
                System.exit(1);
            }
            // index++;
            // continue;
            // }
            if (System.currentTimeMillis() - startingTime > Long.MAX_VALUE) {
                // int oldsize = data.backwardBDDs.size();
                // if (data.backwardBDDs.size() < index + 1) {
                // System.out.println("Error in ending of buildPDB!");
                // System.exit(1);
                // data.backwardBDDs.setSize(index + 1);
                // for (int i = oldsize; i < index + 1; i++)
                // data.backwardBDDs.set(i, factory.zero());
                // }
                try {
                    existingPDBs.close();
                } catch (Exception e) {
                    System.err.println("Error: " + e.getMessage());
                    e.printStackTrace();
                    System.exit(1);
                }
                break;
            }
            searchStep(index, cubep, s2sp, data);
            String pdbFileName = partitionFileName.substring(0,
                    partitionFileName.lastIndexOf(".") - 4)
                    + "PDB_";
            try {
                tmp1 = data.backwardBDDs.get(index).replace(sp2s);
                // data.backwardBDDs.get(index).free();
                data.backwardBDDs.remove(index).free();
                // data.backwardBDDs.set(index, factory.zero());
                String fullPDBFileName = pdbFileName + index;
                factory.save(fullPDBFileName, tmp1);
                if (calculateAverage) {
                    currentSize = (double) tmp1.satCount(cubep);
                    // System.out.println(currentSize);
                    factor = heuristicSize / (heuristicSize + currentSize);
                    averageHeuristic *= factor;
                    heuristicSize += currentSize;
                    additional = index * currentSize / heuristicSize;
                    averageHeuristic += additional;
                }
                existingPDBs.write(fullPDBFileName + "\n");
                existingPDBs.flush();
                maxPDB.write(index + "\n");
                maxPDB.flush();
                tmp1.free();
            } catch (Exception e) {
                System.err.println("Error: " + e.getMessage());
                System.exit(1);
            }
            index++;

            // use of super pdb
            if (useSuperPDB && index < superPDBSize) {
                System.out.println("index: " + index);
                tmp1 = data.backwardBDDs.get(index).and(superPDB.get(index));
                if (tmp1.satCount(cube) < superPDB.get(index).satCount(cube)) {
                    tmp1.free();
                    useSuperPDB = false;
                    System.out.println("stopped in step " + index);
                } else {
                    data.backwardBDDs.remove(index).free();
                    data.backwardBDDs.put(index, tmp1);
                }
            }
        }
        if (calculateAverage) {
            currentSize = (long) data.backwardReached.satCount(cube);
            factor = heuristicSize / (heuristicSize + currentSize);
            averageHeuristic *= factor;
            heuristicSize += currentSize;
            additional = index * currentSize / heuristicSize;
            averageHeuristic += additional;
        }
        // System.out.println("   final #nodes: " +
        // data.backwardReached.nodeCount()
        // + "; #sat: " + currentSize);
        data.backwardReached.free();
        System.out.println("average heuristic value: " + averageHeuristic);
        return averageHeuristic;
    }

    public void buildSuperPDB() {
        long startingTime = System.currentTimeMillis();
        HashMap<Integer, BDD> backwardBDDs = new HashMap<Integer, BDD>();
        int index;
        BDD tmp1;
        DijkstraData data = new DijkstraData();

        index = 0;
        // backwardBDDs.setSize(maxCost + 1);
        backwardBDDs.put(index, trueGoal.id());
        // for (int i = 1; i < maxCost + 1; i++)
        // backwardBDDs.set(i, factory.zero());
        data.backwardReached = factory.zero();
        data.backwardBDDs = backwardBDDs;
        while (!data.backwardBDDs.isEmpty()) {
            // while (index < data.backwardBDDs.size()) {
            index = Collections.min(data.backwardBDDs.keySet());
            System.out.println("   step: " + index);
            // if (data.backwardBDDs.get(index).equals(factory.zero())) {
            // index++;
            // continue;
            // }
            if (System.currentTimeMillis() - startingTime > 100 * 1000
                    || index == 4) {
                // int oldsize = data.backwardBDDs.size();
                // if (data.backwardBDDs.size() < index + 1) {
                // System.out.println("Error in ending of buildSuperPDB!");
                // System.exit(1);
                // data.backwardBDDs.setSize(index + 1);
                // for (int i = oldsize; i < index + 1; i++)
                // data.backwardBDDs.set(i, factory.zero());
                // }
                break;
            }
            searchStep(index, cubep, s2sp, data);
            String pdbFileName = partitionFileName.substring(0,
                    partitionFileName.lastIndexOf(".") - 4)
                    + "PDB_";
            try {
                tmp1 = data.backwardBDDs.get(index).replace(sp2s);
                // data.backwardBDDs.get(index).free();
                data.backwardBDDs.remove(index).free();
                // data.backwardBDDs.set(index, factory.zero());
                data.backwardBDDs.put(index, factory.zero());
                factory.save(pdbFileName + (index), tmp1);
                tmp1.free();
            } catch (Exception e) {
                System.err.println("Error: " + e.getMessage());
                System.exit(1);
            }
        }
        System.out.println("   final #nodes: "
                + data.backwardReached.nodeCount() + "; #sat: "
                + (long) data.backwardReached.satCount(cube));
        data.backwardReached.free();
    }
}
