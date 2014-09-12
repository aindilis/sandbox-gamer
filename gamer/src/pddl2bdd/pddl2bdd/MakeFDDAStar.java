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
 * This class not only creates the BDDs but also allows symbolic A* search. It
 * also performs solution reconstruction and writes an optimal plan into the
 * file "plan_output".
 * 
 * @author Peter Kissmann
 * @version 1.7
 */
public class MakeFDDAStar {
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
    private LinkedList<HashMap<Integer, BDD>> pdbs;
    private HashMap<Integer, LinkedList<BDD>> heuristicToPDBs;
    private int maxH;

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
    public MakeFDDAStar(LinkedList<LinkedList<String>> partitions,
            int numberOfVars, String library, String partitionFileName) {
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
        File file = new File("usePDBs.txt");
        LinkedList<String> pdbsToUse = new LinkedList<String>();
        if (file.exists()) {
            try {
                BufferedReader bufferedReader = new BufferedReader(
                        new FileReader("usePDBs.txt"));
                String line;
                while ((line = bufferedReader.readLine()) != null) {
                    pdbsToUse.add(line);
                }
                bufferedReader.close();
            } catch (Exception e) {
                System.err.println("Error: " + e.getMessage());
                e.printStackTrace();
            }
        }
        actionNames = new HashMap<Integer, LinkedList<String>>();
        t = new HashMap<Integer, LinkedList<BDD>>();
        actionCosts = new LinkedList<Integer>();
        boolean bddsStored = false;
        file = new File("goal");
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
            // load the PDBs to find out if some action costs need to be adapted
            ListIterator<Action> actionIt;
            if (pdbsToUse.size() > 1) {
                int[] actionCostFactors = new int[GroundedPDDLParser.actions
                        .size()];
                try {
                    ListIterator<String> usePDBsIt = pdbsToUse.listIterator();
                    int number;
                    int actionIndex;
                    while (usePDBsIt.hasNext()) {
                        actionIndex = 0;
                        BufferedReader bufferedReader = new BufferedReader(
                                new FileReader("abstract"
                                        + usePDBsIt.next()
                                        + partitionFileName.substring(
                                                partitionFileName.indexOf("-"),
                                                partitionFileName
                                                        .lastIndexOf(".") - 4)
                                        + "UsedActions.txt"));
                        while ((number = bufferedReader.read()) != -1) {
                            if (number == 49) { // 1
                                actionCostFactors[actionIndex]++;
                                actionIndex++;
                            } else if (number == 48) // 0
                                actionIndex++;
                        }
                    }
                    for (int i = 0; i < actionCostFactors.length; i++) {
                        if (actionCostFactors[i] == 0)
                            actionCostFactors[i] = 1;
                    }
                    actionIndex = 0;
                    actionIt = GroundedPDDLParser.actions.listIterator();
                    while (actionIt.hasNext()) {
                        Action action = actionIt.next();
                        action.setCost(action.getCost()
                                * actionCostFactors[actionIndex]);
                        actionIndex++;
                    }
                } catch (Exception e) {
                    System.err.println("Error: " + e.getMessage());
                    e.printStackTrace();
                }
            }

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

        // read PDBs
        System.out.println("   reading PDBs ...");
        String filename;
        pdbs = new LinkedList<HashMap<Integer, BDD>>();
        BDD pdbState;

        int[][] pdbValues = new int[pdbsToUse.size()][];
        int pdbIndex = 0;
        ListIterator<String> usePDBIt = pdbsToUse.listIterator();
        while (usePDBIt.hasNext()) {
            Vector<Integer> values = new Vector<Integer>();
            String nextPDB = usePDBIt.next();
            filename = "abstract"
                    + nextPDB
                    + partitionFileName.substring(partitionFileName
                            .indexOf("-"),
                            partitionFileName.lastIndexOf(".") - 4)
                    + "ExPDBs.txt";
            System.out.println("      reading PDB abstract"
                    + nextPDB
                    + partitionFileName.substring(partitionFileName
                            .indexOf("-"),
                            partitionFileName.lastIndexOf(".") - 4));
            file = new File(filename);
            try {
                BDD statesNotInPDB = factory.one();
                String filename2 = "abstract"
                        + nextPDB
                        + partitionFileName.substring(partitionFileName
                                .indexOf("-"), partitionFileName
                                .lastIndexOf(".") - 4) + "MaxPDB.txt";
                BufferedReader bufferedReader = new BufferedReader(
                        new FileReader(filename2));
                String line;
                int lastMax = -1;
                while ((line = bufferedReader.readLine()) != null) {
                    lastMax = Integer.parseInt(line);
                }
                bufferedReader.close();
                HashMap<Integer, BDD> newPDB = new HashMap<Integer, BDD>();
                bufferedReader = new BufferedReader(new FileReader(filename));
                while ((line = bufferedReader.readLine()) != null) {
                    file = new File(line);
                    String[] lineParts = line.split("_");
                    int index = Integer.parseInt(lineParts[1]);
                    if (file.exists()) {
                        pdbState = factory.load(line);
                        newPDB.put(index, pdbState);
                        BDD tmp1 = pdbState.not();
                        BDD tmp2 = statesNotInPDB;
                        statesNotInPDB = tmp2.and(tmp1);
                        tmp1.free();
                        tmp2.free();
                        values.add(index);
                    }
                }
                bufferedReader.close();
                if (!statesNotInPDB.equals(factory.zero())) {
                    newPDB.put(lastMax + 1, statesNotInPDB);
                    values.add(lastMax + 1);
                }
                pdbs.add(newPDB);
                pdbValues[pdbIndex] = new int[values.size()];
                for (int i = 0; i < values.size(); i++) {
                    pdbValues[pdbIndex][i] = values.elementAt(i);
                }
                pdbIndex++;
            } catch (Exception e) {
                System.err.println("Error: " + e.getMessage());
                e.printStackTrace();
                System.exit(1);
            }
        }
        heuristicToPDBs = new HashMap<Integer, LinkedList<BDD>>();
        if (pdbs.size() == 0) {
            System.err.println("Warning: no PDB-files found!");
            System.err.println("Using empty PDB!");
            LinkedList<BDD> tmpList = new LinkedList<BDD>();
            tmpList.add(factory.one());
            heuristicToPDBs.put(0, tmpList);
        } else {
            int indices[] = new int[pdbValues.length];
            findAllHeuristicValues(heuristicToPDBs, pdbValues, indices);
            ListIterator<HashMap<Integer, BDD>> pdbsIt = pdbs.listIterator();
            while (pdbsIt.hasNext()) {
                HashMap<Integer, BDD> pdb = pdbsIt.next();
                Collection<BDD> pdbBDDs = pdb.values();
                Iterator<BDD> bddIt = pdbBDDs.iterator();
                while (bddIt.hasNext()) {
                    bddIt.next().free();
                }
            }
        }
        System.out.println("   done.");

        // build heuristic
        System.out.println("   building the heuristic ...");
        maxH = 0;
        for (int i = 0; i < pdbs.size(); i++) {
            maxH += Collections.max(pdbs.get(i).keySet());
        }
        System.out.println("   done.");
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
        Collection<Integer> hValues = heuristicToPDBs.keySet();
        Iterator<Integer> hValueIt = hValues.iterator();
        while (hValueIt.hasNext()) {
            LinkedList<BDD> pdbBDD = heuristicToPDBs.get(hValueIt.next());
            ListIterator<BDD> pdbBDDIt = pdbBDD.listIterator();
            while (pdbBDDIt.hasNext()) {
                pdbBDDIt.next().free();
            }
        }
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

    private class AStarData {
        public BDD forwardReached;
        public Vector<BDD> forwardBDDs;
    }

    private Vector<BDD> searchStep(int index, Vector<BDD> frontier,
            BDDVarSet varSet, BDDPairing pairing, AStarData data) {
        BDD tmp1;
        BDD tmp2;
        BDD negatedReached;
        BDD to;
        int currentSize;
        BDD totalFrontier = frontier.get(0).id();
        BDD oldFrontier;

        negatedReached = data.forwardReached.not();
        if (t.containsKey(0)) {
            while (true) {
                tmp1 = image(0, frontier.lastElement(), varSet);
                to = tmp1.replace(pairing);
                tmp1.free();
                tmp1 = to.and(negatedReached);
                to.free();
                oldFrontier = totalFrontier;
                tmp2 = oldFrontier.not();
                BDD tmp3 = tmp1.and(tmp2);
                if (tmp3.equals(factory.zero())) {
                    tmp1.free();
                    tmp2.free();
                    break;
                }
                frontier.add(tmp1.and(tmp2));
                tmp1.free();
                tmp2.free();
                tmp3.free();
                totalFrontier = oldFrontier.or(frontier.lastElement());
                oldFrontier.free();
            }
        } else {
            tmp1 = totalFrontier;
            totalFrontier = tmp1.and(negatedReached);
            tmp1.free();
        }

        negatedReached.free();
        if (data.forwardReached.equals(factory.zero()))
            data.forwardReached = totalFrontier.id();
        else {
            tmp1 = data.forwardReached;
            data.forwardReached = tmp1.or(totalFrontier);
            tmp1.free();
        }

        int d;
        ListIterator<Integer> costIt = actionCosts.listIterator();
        while (costIt.hasNext()) {
            d = costIt.next();
            tmp1 = image(d, totalFrontier, varSet);
            to = tmp1.replace(pairing);
            tmp1.free();
            currentSize = data.forwardBDDs.size();
            if (currentSize <= index + d) {
                data.forwardBDDs.setSize(index + d + 1);
                for (int i = currentSize; i < index + d + 1; i++)
                    data.forwardBDDs.set(i, factory.zero());
            }
            tmp1 = data.forwardBDDs.get(index + d);
            data.forwardBDDs.set(index + d, tmp1.or(to));
            tmp1.free();
            to.free();
        }
        totalFrontier.free();
        return frontier;
    }

    public void findPlanAStar() {
        Vector<Vector<Vector<BDD>>> forwardBDD = new Vector<Vector<Vector<BDD>>>();
        int fmin = 0;
        BDD foundBDD;
        BDD tmp1;
        BDD tmp2;
        BDD intersection;
        BDD forwardFrontier;
        Vector<Vector<BDD>> solutionBDD = new Vector<Vector<BDD>>();
        BDD replacedGoal = trueGoal.replace(sp2s);
        AStarData data;
        int oldSize;

        data = new AStarData();
        data.forwardReached = factory.zero();
        System.out.println("maximal possible h-value: " + maxH);
        foundBDD = getBDD(fmin, init);
        while (foundBDD.equals(factory.zero())) {
            fmin++;
            if (fmin > maxH) {
                System.out
                        .println("Error: minimal f-value higher than maximal sum of patterns!");
                System.exit(1);
            }
            foundBDD = getBDD(fmin, init);
        }
        foundBDD.free();
        System.out.println("starting f-value: " + fmin);
        forwardBDD.setSize(fmin + 1);
        for (int i = 0; i < fmin + 1; i++) {
            forwardBDD.set(i, new Vector<Vector<BDD>>());
            forwardBDD.get(i).setSize(maxH + 1);
            for (int j = 0; j < maxH + 1; j++) {
                forwardBDD.get(i).set(j, new Vector<BDD>());
                forwardBDD.get(i).get(j).setSize(1);
                forwardBDD.get(i).get(j).set(0, factory.zero());
            }
        }
        forwardBDD.get(0).get(fmin).set(0, init.id());
        solutionBDD.setSize(maxH + 1);
        for (int i = 0; i < maxH + 1; i++) {
            solutionBDD.set(i, new Vector<BDD>());
        }
        intersection = init.and(replacedGoal);
        while (intersection.equals(factory.zero())) {
            System.out.println("   fmin: " + fmin);
            for (int gmin = 0; gmin <= fmin; gmin++) {
                if (gmin >= forwardBDD.size())
                    break;
                int hmax = fmin - gmin;
                if (hmax >= forwardBDD.get(gmin).size())
                    continue;
                if (!forwardBDD.get(gmin).get(hmax).equals(factory.zero())) {
                    System.out.println("     gmin: " + gmin);
                    while (gmin >= solutionBDD.size()) {
                        int currentSize = solutionBDD.size();
                        solutionBDD.setSize(currentSize * 2);
                        for (int i = currentSize; i < currentSize * 2; i++) {
                            solutionBDD.set(i, new Vector<BDD>());
                        }
                    }
                    Vector<BDD> temp;
                    temp = new Vector<BDD>();
                    temp.add(factory.zero());
                    data.forwardBDDs = temp;
                    searchStep(0, forwardBDD.get(gmin).get(hmax), cube, sp2s,
                            data);

                    tmp1 = factory.zero();
                    for (int i = 0; i < solutionBDD.get(gmin).size(); i++) {
                        tmp2 = tmp1;
                        tmp1 = tmp2.or(solutionBDD.get(gmin).get(i));
                        tmp2.free();
                    }
                    tmp2 = tmp1.not();
                    tmp1.free();
                    forwardFrontier = factory.zero();
                    for (int i = 0; i < forwardBDD.get(gmin).get(hmax).size(); i++) {
                        tmp1 = forwardBDD.get(gmin).get(hmax).get(i);
                        forwardBDD.get(gmin).get(hmax).set(i, tmp1.and(tmp2));
                        tmp1.free();
                        tmp1 = forwardFrontier;
                        forwardFrontier = tmp1.or(forwardBDD.get(gmin)
                                .get(hmax).get(i));
                        tmp1.free();
                    }
                    tmp2.free();
                    solutionBDD.get(gmin)
                            .addAll(forwardBDD.get(gmin).get(hmax));
                    intersection = replacedGoal.and(forwardFrontier);
                    if (!intersection.equals(factory.zero())) {
                        forwardFrontier.free();
                        data.forwardReached.free();
                        replacedGoal.free();
                        System.out.println("   cheapest plan has cost of "
                                + gmin);
                        reconstructPlanAStar(solutionBDD, gmin, intersection
                                .replace(s2sp));
                        intersection.free();
                        return;
                    }

                    forwardFrontier.free();

                    oldSize = forwardBDD.size();
                    if (oldSize < gmin + temp.size() + 1) {
                        forwardBDD.setSize(gmin + temp.size() + 1);
                        for (int i = oldSize; i < gmin + temp.size() + 1; i++) {
                            forwardBDD.set(i, new Vector<Vector<BDD>>());
                        }
                    }
                    for (int d = 0; d < temp.size(); d++) {
                        if (temp.get(d).equals(factory.zero()))
                            continue;
                        oldSize = forwardBDD.get(gmin + d).size();
                        if (oldSize < maxH + 1) {
                            forwardBDD.get(gmin + d).setSize(maxH + 1);
                            for (int i = oldSize; i < maxH + 1; i++) {
                                forwardBDD.get(gmin + d).set(i,
                                        new Vector<BDD>());
                                forwardBDD.get(gmin + d).get(i).add(
                                        factory.zero());
                            }
                        }
                        for (int dist = 0; dist <= maxH; dist++) {
                            BDD lookup = /* heur-> */getBDD(dist, temp.get(d));
                            if (lookup.equals(factory.zero()))
                                continue;
                            int newDist = dist;
                            if (newDist < fmin - (gmin + d)) {
                                System.err.print("Error: successor in bucket ("
                                        + (gmin + d) + ", " + newDist
                                        + ") left of f-diagonal (" + fmin
                                        + ") => heuristic not consistent!");
                                System.exit(1);
                            }
                            tmp1 = forwardBDD.get(gmin + d).get(newDist).get(0);
                            forwardBDD.get(gmin + d).get(newDist).set(0,
                                    tmp1.or(lookup));
                            tmp1.free();
                            lookup.free();
                        }
                        temp.get(d).free();
                        temp.set(d, factory.zero());
                    }
                }
            }
            fmin++;
        }
        replacedGoal.free();
        intersection.free();
        data.forwardReached.free();
        for (int i = 0; i < forwardBDD.size(); i++)
            for (int j = 0; j < forwardBDD.get(i).size(); j++)
                for (int k = 0; k < forwardBDD.get(i).get(j).size(); k++)
                    forwardBDD.get(i).get(j).get(k).free();
    }

    public void findPlanAStarNew() {
        HashMap<Integer, HashMap<Integer, BDD>> searchSpace;
        HashMap<Integer, BDD> fDiagonal;
        int fmin = -1;
        BDD foundBDD = factory.zero();
        BDD tmp1;
        BDD tmp2;
        BDD intersection;
        BDD forwardFrontier;
        Vector<Vector<BDD>> solutionBDD = new Vector<Vector<BDD>>();
        BDD replacedGoal = trueGoal.replace(sp2s);
        AStarData data;

        data = new AStarData();
        data.forwardReached = factory.zero();
        System.out.println("maximal possible h-value: " + maxH);
        Set<Integer> keySet = heuristicToPDBs.keySet();
        fmin = Collections.min(keySet);
        List<Integer> allKeys = sortCollection(keySet);
        ListIterator<Integer> keysIt = allKeys.listIterator();
        while (keysIt.hasNext()) {
            fmin = keysIt.next();
            foundBDD = getBDD(fmin, init);
            if (!foundBDD.equals(factory.zero()))
                break;
        }
        if (foundBDD.equals(factory.zero())) {
            System.out
                    .println("Error: initial state not found in pattern database!");
            System.exit(1);
        }
        foundBDD.free();
        System.out.println("starting f-value: " + fmin);
        fDiagonal = new HashMap<Integer, BDD>();
        fDiagonal.put(0, init.id());
        searchSpace = new HashMap<Integer, HashMap<Integer, BDD>>();
        searchSpace.put(fmin, fDiagonal);
        solutionBDD.setSize(maxH + 1);
        for (int i = 0; i < maxH + 1; i++) {
            solutionBDD.set(i, new Vector<BDD>());
        }
        intersection = init.and(replacedGoal);
        while (intersection.equals(factory.zero())) {
            fmin = Collections.min(searchSpace.keySet());
            fDiagonal = searchSpace.get(fmin);
            // if (searchSpace.containsKey(fmin))
            // fDiagonal = searchSpace.get(fmin);
            // else {
            // fmin++;
            // continue;
            // }
            // int gmin = 0;
            int gmin;
            while (!fDiagonal.isEmpty()) {
                gmin = Collections.min(fDiagonal.keySet());
                // if (fDiagonal.containsKey(gmin)) {
                // System.out.println("     gmin: " + gmin);
                while (gmin >= solutionBDD.size()) {
                    int currentSize = solutionBDD.size();
                    solutionBDD.setSize(currentSize * 2);
                    for (int i = currentSize; i < currentSize * 2; i++) {
                        solutionBDD.set(i, new Vector<BDD>());
                    }
                }
                Vector<BDD> temp;
                temp = new Vector<BDD>();
                temp.add(factory.zero());
                data.forwardBDDs = temp;
                Vector<BDD> fgVector = new Vector<BDD>();
                fgVector.add(fDiagonal.remove(gmin));
                searchStep(0, fgVector, cube, sp2s, data);

                tmp1 = factory.zero();
                for (int i = 0; i < solutionBDD.get(gmin).size(); i++) {
                    tmp2 = tmp1;
                    tmp1 = tmp2.or(solutionBDD.get(gmin).get(i));
                    tmp2.free();
                }
                tmp2 = tmp1.not();
                tmp1.free();
                forwardFrontier = factory.zero();
                for (int i = 0; i < fgVector.size(); i++) {
                    tmp1 = fgVector.get(i);
                    fgVector.set(i, tmp1.and(tmp2));
                    tmp1.free();
                    tmp1 = forwardFrontier;
                    forwardFrontier = tmp1.or(fgVector.get(i));
                    tmp1.free();
                }
                tmp2.free();
                solutionBDD.get(gmin).addAll(fgVector);
                intersection = replacedGoal.and(forwardFrontier);
                if (!intersection.equals(factory.zero())) {
                    forwardFrontier.free();
                    data.forwardReached.free();
                    replacedGoal.free();
                    for (int i = 0; i < data.forwardBDDs.size(); i++) {
                        data.forwardBDDs.elementAt(i).free();
                    }
                    Iterator<Integer> searchSpaceIt = searchSpace.keySet()
                            .iterator();
                    while (searchSpaceIt.hasNext()) {
                        HashMap<Integer, BDD> searchLayer = searchSpace
                                .get(searchSpaceIt.next());
                        Iterator<Integer> layerIt = searchLayer.keySet()
                                .iterator();
                        while (layerIt.hasNext()) {
                            searchLayer.get(layerIt.next()).free();
                        }
                    }
                    System.out.println("   cheapest plan has cost of " + gmin);
                    reconstructPlanAStar(solutionBDD, gmin, intersection
                            .replace(s2sp));
                    intersection.free();
                    return;
                }

                forwardFrontier.free();

                for (int d = 0; d < temp.size(); d++) {
                    if (temp.get(d).equals(factory.zero()))
                        continue;
                    keysIt = allKeys.listIterator();
                    while (keysIt.hasNext()) {
                        int dist = keysIt.next();
                        BDD lookup = getBDD(dist, temp.get(d));
                        if (lookup.equals(factory.zero()))
                            continue;
                        int newDist = dist;
                        if (newDist < fmin - (gmin + d)) {
                            System.err.print("Error: successor in bucket ("
                                    + (gmin + d) + ", " + newDist
                                    + ") left of f-diagonal (" + fmin
                                    + ") => heuristic not consistent!");
                            System.exit(1);
                        }
                        HashMap<Integer, BDD> succDiagonal;
                        if (searchSpace.containsKey(gmin + d + newDist)) {
                            succDiagonal = searchSpace.get(gmin + d + newDist);
                            if (succDiagonal.containsKey(gmin + d)) {
                                tmp1 = succDiagonal.remove(gmin + d);
                                succDiagonal.put(gmin + d, tmp1.or(lookup));
                                tmp1.free();
                                lookup.free();
                            } else {
                                succDiagonal.put(gmin + d, lookup);
                            }
                        } else {
                            succDiagonal = new HashMap<Integer, BDD>();
                            succDiagonal.put(gmin + d, lookup);
                            searchSpace.put(gmin + d + newDist, succDiagonal);
                        }
                    }
                    temp.get(d).free();
                    temp.set(d, factory.zero());
                }
                // }
                // gmin++;
            }
            searchSpace.remove(fmin);
            // fmin++;
        }
        replacedGoal.free();
        intersection.free();
        data.forwardReached.free();
        // cleanup searchspace!
    }

    private void reconstructPlanAStar(Vector<Vector<BDD>> forwardBDDs,
            int index, BDD start) {
        LinkedList<String> solution = new LinkedList<String>();

        System.out.println("   reconstructing cheapest plan ...");
        for (int i = forwardBDDs.size() - 1; i > index; i--) {
            Vector<BDD> forwardLayer = forwardBDDs.elementAt(i);
            for (int j = forwardLayer.size() - 1; j >= 0; j--)
                forwardLayer.remove(j).free();
            forwardBDDs.remove(i);
        }

        // calculate plan
        if (t.containsKey(0))
            actionCosts.addFirst(0);
        Collections.reverse(actionCosts);
        reconstructPlanBackwardAStar(index, forwardBDDs, start, solution);
        for (int i = forwardBDDs.size() - 1; i >= 0; i--) {
            Vector<BDD> forwardLayer = forwardBDDs.elementAt(i);
            for (int j = forwardLayer.size() - 1; j >= 0; j--)
                forwardLayer.remove(j).free();
            forwardBDDs.remove(i);
        }

        // print plan
        try {
            FileWriter writer = new FileWriter("plan_output");
            int initialOutputCapacity = 10000;
            StringBuilder output = new StringBuilder(initialOutputCapacity);
            int counter = 0;
            while (!solution.isEmpty()) {
                String nextAction = solution.removeLast();
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
        } catch (Exception e) {
            System.err.println("Error: " + e.getMessage());
            e.printStackTrace(System.err);
            System.exit(1);
        }
        System.out.println("   done.");
    }

    private void reconstructPlanBackwardAStar(int index,
            Vector<Vector<BDD>> solutionPath, BDD start,
            LinkedList<String> solution) {
        BDD tmp1;
        BDD tmp2;
        BDD intermediate;
        BDD newStart = factory.zero();
        int newIndex = -1;
        LinkedList<BDD> t_i;
        int size;
        boolean stop = false;
        boolean totalStop = false;

        tmp2 = start.replace(sp2s);
        for (int i = 0; i < solutionPath.get(index).size(); i++) {
            tmp1 = solutionPath.get(index).get(i).and(tmp2);
            if (!tmp1.equals(factory.zero())) {
                tmp1.free();
                size = solutionPath.get(index).size();
                for (int j = i; j < size; j++) {
                    solutionPath.get(index).remove(i).free();
                }
                break;
            }
        }
        tmp2.free();

        int d;
        ListIterator<Integer> costIt = actionCosts.listIterator();
        while (costIt.hasNext()) {
            d = costIt.next();
            if (d > index)
                continue;
            newIndex = index - d;
            t_i = t.get(d);
            size = t_i.size();
            for (int i = 0; i < size; i++) {
                intermediate = t_i.get(i).relprod(start, cubep);
                for (int j = 0; j < solutionPath.get(newIndex).size(); j++) {
                    tmp1 = intermediate.and(solutionPath.get(newIndex).get(j));
                    if (!tmp1.equals(factory.zero())) {
                        newStart = tmp1.replace(s2sp);
                        tmp2 = intermediate.and(init);
                        if (!tmp2.equals(factory.zero())) {
                            tmp2.free();
                            totalStop = true;
                        }
                        tmp1.free();
                        for (int k = solutionPath.size() - 1; k > newIndex; k--) {
                            while (!solutionPath.get(k).isEmpty())
                                solutionPath.get(k).remove(0).free();
                            solutionPath.remove(k);
                        }
                        solution.addLast(actionNames.get(d).get(i));
                        stop = true;
                        break;
                    }
                }
                intermediate.free();
                if (stop)
                    break;
            }
            if (stop)
                break;
        }
        start.free();
        if (!totalStop)
            reconstructPlanBackwardAStar(newIndex, solutionPath, newStart,
                    solution);
        else
            newStart.free();
    }

    private BDD getBDD(int index, BDD in) {
        BDD result = factory.zero();
        LinkedList<BDD> pdbList = heuristicToPDBs.get(index);
        ListIterator<BDD> pdbListIt = pdbList.listIterator();
        while (pdbListIt.hasNext()) {
            result = in.and(pdbListIt.next());
            if (!result.equals(factory.zero()))
                break;
        }
        return result;
    }

    private void findAllHeuristicValues(
            HashMap<Integer, LinkedList<BDD>> heuristicValues,
            int[][] pdbHeuristics, int[] indices) {
        int key;
        boolean finished = false;
        int currentIndex;
        ListIterator<Integer> combIt;
        ListIterator<HashMap<Integer, BDD>> pdbIt;
        BDD check;
        BDD tmp1;
        while (!finished) {
            key = 0;
            finished = true;
            LinkedList<Integer> heuristicCombination = new LinkedList<Integer>();
            for (currentIndex = 0; currentIndex < indices.length; currentIndex++) {
                key += pdbHeuristics[currentIndex][indices[currentIndex]];
                heuristicCombination
                        .add(pdbHeuristics[currentIndex][indices[currentIndex]]);
                if (indices[currentIndex] == pdbHeuristics[currentIndex].length - 1) {
                    indices[currentIndex] = 0;
                } else {
                    indices[currentIndex]++;
                    finished = false;
                    break;
                }
            }
            currentIndex++;
            for (; currentIndex < indices.length; currentIndex++) {
                key += pdbHeuristics[currentIndex][indices[currentIndex]];
                heuristicCombination
                        .add(pdbHeuristics[currentIndex][indices[currentIndex]]);
            }

            // check, if conjunction of PDBs is not \bot
            combIt = heuristicCombination.listIterator();
            pdbIt = pdbs.listIterator();
            check = factory.one();
            while (combIt.hasNext()) {
                tmp1 = check;
                int index = combIt.next();
                check = tmp1.and(pdbIt.next().get(index));
                tmp1.free();
                if (check.equals(factory.zero())) {
                    break;
                }
            }
            if (check.equals(factory.zero()))
                continue;

            if (heuristicValues.containsKey(key)) {
                heuristicValues.get(key).add(check);
            } else {
                LinkedList<BDD> newHeuristicValue = new LinkedList<BDD>();
                newHeuristicValue.add(check);
                heuristicValues.put(key, newHeuristicValue);
            }
        }
    }

    public static <T extends Comparable<? super T>> List<T> sortCollection(
            Collection<T> c) {
        List<T> list = new ArrayList<T>(c);
        java.util.Collections.sort(list);
        return list;
    }

}
