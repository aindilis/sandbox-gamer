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
import java.util.ListIterator;
import java.util.Vector;
import java.util.HashSet;

import net.sf.javabdd.BDD;
import net.sf.javabdd.BDDFactory;

/**
 * @author Peter Kissmann
 * @version 2.0
 */
public class Condition extends Expression {
    @Override
    public BDD createBDD(BDDFactory factory, LinkedList<String> nAryVariables,
                         LinkedList<BDD> nAryVariablesPreBDDs, LinkedList<BDD> nAryVariablesEffBDDs, boolean usePreVars, boolean[] unusedVarIndices) {
        // BDD tmp1;
        // BDD tmp2;
        // BDD ret;
        // tmp1 = pre.createBDD(factory, nAryVariables, nAryVariablesPreBDDs, nAryVariablesPreBDDs, true, unusedVarIndices);
        // if (tmp1 == null)
        //     tmp1 = factory.one();
        // tmp2 = eff.createBDD(factory, nAryVariables, nAryVariablesEffBDDs, nAryVariablesEffBDDs, false, unusedVarIndices);
        // if (tmp2 == null) {
        //     tmp1.free();
        //     return null;
        // }
        // System.out.print("pre: ");
        // tmp1.printSet();
        // System.out.print("eff: ");
        // tmp2.printSet();
        // //ret = tmp1.imp(tmp2);
        // ret = tmp1.and(tmp2); // biimplication, or what else?!
        // tmp1.free();
        // tmp2.free();
        // return ret;
        return null; // conditional effects will be handled separately
    }

    public BDD createPreBDD(BDDFactory factory, LinkedList<String> nAryVariables,
                            LinkedList<BDD> nAryVariablesPreBDDs, boolean[] unusedVarIndices) {
        BDD ret;
        ret = pre.createBDD(factory, nAryVariables, nAryVariablesPreBDDs, null, true, unusedVarIndices);
        if (ret == null)
            return factory.one();
        return ret;
    }

    public BDD createEffBDD(BDDFactory factory, LinkedList<String> nAryVariables,
                            LinkedList<BDD> nAryVariablesEffBDDs, boolean[] unusedEffVarIndices) {
        BDD ret;
        ret = eff.createBDD(factory, nAryVariables, null, nAryVariablesEffBDDs, false, unusedEffVarIndices);
        return ret;
    }

    @Override
    public void classifyEffects(HashSet<String> addEffects,
                                HashSet<String> delEffects, Vector<Condition> condEffects, Vector<HashSet<String>> condEffectVars, boolean isNegated, boolean inCondEffect) {
        condEffects.add(this);
        condEffectVars.add(new HashSet<String>());
        eff.classifyEffects(addEffects, delEffects, condEffects, condEffectVars, isNegated, true);
    }

    @Override
    public void getAllPredicates(Vector<Predicate> allPreds) {
        eff.getAllPredicates(allPreds);
    }

    @Override
    public void findDelAdds(HashSet<String> delEffects,
            HashSet<String> addEffects, boolean isPositive) {
        //System.err.println("Warning: elimination of delete effects in conditional effects not yet implemented!");
    }

    @Override
    public boolean eliminateDelEffects(HashSet<String> delEffectsToEliminate,
            boolean isPositive) {
        //System.err.println("Warning: elimination of delete effects in conditional effects not yet implemented!");
        return false;
    }

    @Override
    public String toString() {
        String ret;
        ret = "(when\n";
        ret += pre.toString() + "\n";
        ret += eff.toString() + "\n";
        ret += ")";
        return ret;
    }

    public void setPre(Expression pre) {
        this.pre = pre;
    }

    public Expression getPre() {
        return pre;
    }

    public void setEff(Expression eff) {
        this.eff = eff;
    }

    public Expression getEff() {
        return eff;
    }

    public void createSyntaxTree(SyntaxTreeNode node, SyntaxTree tree, LinkedList<LinkedList<String>> partitions) {
        SyntaxTreeNode whenNode = new SyntaxTreeNode();
        node.addSuccessor(whenNode);
        pre.createSyntaxTree(whenNode, tree, partitions);
        eff.createSyntaxTree(whenNode, tree, partitions);
    }

    /*public void splitConditionalEffect(LinkedList<LinkedList<String>> partitions) {
        eff.splitEffects(partitions);
    }

    public void splitEffect(LinkedList<LinkedList<String>> partitions) {
        // cannot have nested conditional effects
        System.err.println("Cannot have nested conditional effects!");
        System.exit(1);
        }*/

    private Expression pre;
    private Expression eff;
}
