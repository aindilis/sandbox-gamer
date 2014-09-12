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

import java.util.LinkedList;
import java.util.Vector;
import java.util.HashSet;

import net.sf.javabdd.*;

/**
 * @author Peter Kissmann
 * @version 2.0
 */
public abstract class Expression {
    public abstract BDD createBDD(BDDFactory factory, LinkedList<String> nAryVariables,
                                  LinkedList<BDD> nAryVariablesPreBDDs, LinkedList<BDD> nAryVariablesEffBDDs, boolean usePreVars, boolean[] unusedVarIndices);

    public abstract void classifyEffects(HashSet<String> addEffects,
                                         HashSet<String> delEffects, Vector<Condition> condEffects, Vector<HashSet<String>> condEffectVars, boolean isNegated, boolean inCondEffect);

    public abstract void getAllPredicates(Vector<Predicate> allPreds);

    public abstract void findDelAdds(HashSet<String> delEffects,
            HashSet<String> addEffects, boolean isPositive);

    public abstract boolean eliminateDelEffects(
            HashSet<String> delEffectsToEliminate, boolean isPositive);

    public abstract void createSyntaxTree(SyntaxTreeNode node, SyntaxTree tree, LinkedList<LinkedList<String>> partitions);

    public abstract String toString();

    /*public abstract void splitConditionalEffect(LinkedList<LinkedList<String>> partitions);*/
}
