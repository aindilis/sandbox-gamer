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

import net.sf.javabdd.BDD;
import net.sf.javabdd.BDDFactory;

/**
 * @author Peter Kissmann
 * @version 2.0
 */
public class NotTerm extends Expression {
    @Override
    public BDD createBDD(BDDFactory factory, LinkedList<String> nAryVariables,
                         LinkedList<BDD> nAryVariablesPreBDDs, LinkedList<BDD> nAryVariablesEffBDDs, boolean usePreVars, boolean[] unusedVarIndices) {
        BDD tmp = term.createBDD(factory, nAryVariables, nAryVariablesPreBDDs, nAryVariablesEffBDDs, usePreVars,
                unusedVarIndices);
        if (tmp == null)
            return null;
        BDD ret = tmp.not();
        tmp.free();
        return ret;
    }

    @Override
    public void classifyEffects(HashSet<String> addEffects,
                                HashSet<String> delEffects, Vector<Condition> condEffects, Vector<HashSet<String>> condEffectVars, boolean isNegated, boolean inCondEffect) {
        term.classifyEffects(addEffects, delEffects, condEffects, condEffectVars, !isNegated, inCondEffect);
    }

    @Override
    public void getAllPredicates(Vector<Predicate> allPreds) {
        term.getAllPredicates(allPreds);
    }

    @Override
    public void findDelAdds(HashSet<String> delEffects,
            HashSet<String> addEffects, boolean isPositive) {
        term.findDelAdds(delEffects, addEffects, !isPositive);
    }

    @Override
    public boolean eliminateDelEffects(HashSet<String> delEffectsToEliminate,
            boolean isPositive) {
        return term.eliminateDelEffects(delEffectsToEliminate, !isPositive);
    }

    @Override
    public String toString() {
        String ret = "(not\n" + term.toString() + "\n)";
        return ret;
    }

    public void setTerm(Expression term) {
        this.term = term;
    }

    public Expression getTerm() {
        return term;
    }

    public void createSyntaxTree(SyntaxTreeNode node, SyntaxTree tree, LinkedList<LinkedList<String>> partitions) {
        SyntaxTreeNode notNode = new SyntaxTreeNode();
        node.addSuccessor(notNode);
        term.createSyntaxTree(notNode, tree, partitions);
    }

    /*public void splitConditionalEffect(LinkedList<LinkedList<String>> partitions) {
        // conditional effects may not appear within negations
        return;
        }*/

    private Expression term;
}
