/*
 * Gamer, a tool for finding optimal plans
 * Copyright (C) 2007-2013 by Peter Kissmann
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

package pddl2bdd.parser.logic;

import pddl2bdd.variableOrdering.*;

import java.util.*;

import net.sf.javabdd.BDD;
import net.sf.javabdd.BDDFactory;

/**
 * @author Peter Kissmann
 * @version 2.0
 */
public class Predicate extends Expression {
    @Override
    public BDD createBDD(BDDFactory factory, LinkedList<String> nAryVariables,
                         LinkedList<BDD> nAryVariablesPreBDDs, LinkedList<BDD> nAryVariablesEffBDDs, boolean usePreVars, boolean[] unusedVarIndices) {
        if (name.equalsIgnoreCase("foo"))
            return factory.one();
        if (index == -1)
            index = nAryVariables.indexOf(name);
        if (unusedVarIndices[index])
            return null;
        if (usePreVars)
            return nAryVariablesPreBDDs.get(index).id();
        else
            return nAryVariablesEffBDDs.get(index).id();
    }

    @Override
    public void classifyEffects(HashSet<String> addEffects,
                                HashSet<String> delEffects, Vector<Condition> condEffects, Vector<HashSet<String>> condEffectVars, boolean isNegated, boolean inCondEffect) {
        if (inCondEffect) {
            condEffectVars.lastElement().add(name);
        } else if (!addEffects.contains(name)) {
            if (isNegated)
                delEffects.add(name);
            else
                addEffects.add(name);
        }
    }

    @Override
    public void getAllPredicates(Vector<Predicate> allPreds) {
        if (!allPreds.contains(this))
            allPreds.add(this);
    }

    @Override
    public void findDelAdds(HashSet<String> delEffects,
            HashSet<String> addEffects, boolean isPositive) {
        if (isPositive)
            addEffects.add(name);
        else
            delEffects.add(name);
    }

    @Override
    public boolean eliminateDelEffects(HashSet<String> delEffectsToEliminate,
            boolean isPositive) {
        if (!isPositive && delEffectsToEliminate.contains(name))
            return true;
        return false;
    }

    @Override
    public String toString() {
        String ret = "(" + name + ")";
        return ret;
    }

    public void setName(String name) {
        this.name = name;
    }

    public String getName() {
        return name;
    }

    public int getIndex() {
        return index;
    }

    public void createSyntaxTree(SyntaxTreeNode node, SyntaxTree tree, LinkedList<LinkedList<String>> partitions) {
        ListIterator<LinkedList<String>> partitionsIt = partitions.listIterator();
        int index = 0;
        while (partitionsIt.hasNext()) {
            if (partitionsIt.next().contains(name))
                break;
            index++;
        }
        SyntaxTreeLeaf leaf = new SyntaxTreeLeaf(index);
        node.addSuccessor(leaf);
        node.addVariable(index);
        tree.addLeaf(leaf);
    }

    /*public void splitConditionalEffect(LinkedList<LinkedList<String>> partitions) {
        // conditional effects cannot appear within predicates
        return;
        }*/

    private String name;
    private int index = -1;
}
