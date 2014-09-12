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
public class AndOrTerm extends Expression {
    @Override
    public BDD createBDD(BDDFactory factory, LinkedList<String> nAryVariables,
                         LinkedList<BDD> nAryVariablesPreBDDs, LinkedList<BDD> nAryVariablesEffBDDs, boolean usePreVars, boolean[] unusedVarIndices) {
        if (terms.size() == 0) {
            if (isAndTerm)
                return factory.one();
            else
                return factory.zero();
        }
        if (terms.size() == 1)
            return terms.firstElement().createBDD(factory, nAryVariables,
                                                  nAryVariablesPreBDDs, nAryVariablesEffBDDs, usePreVars, unusedVarIndices);
        BDD tmp1;
        BDD tmp2;
        Vector<BDD> termBDDs = new Vector<BDD>();
        ListIterator<Expression> termsIt = terms.listIterator();
        while (termsIt.hasNext()) {
            tmp1 = termsIt.next().createBDD(factory, nAryVariables,
                                            nAryVariablesPreBDDs, nAryVariablesEffBDDs, usePreVars, unusedVarIndices);
            if (tmp1 != null)
                termBDDs.add(tmp1);
        }
        if (termBDDs.size() == 0)
            return null;
        if (termBDDs.size() == 1)
            return termBDDs.firstElement();

        for (int i = 0; i < termBDDs.size(); i++) {
            tmp1 = termBDDs.get(i);
            i++;
            if (i < termBDDs.size()) {
                tmp2 = termBDDs.get(i);
                if (isAndTerm)
                    termBDDs.add(tmp1.and(tmp2));
                else
                    termBDDs.add(tmp1.or(tmp2));
                tmp1.free();
                tmp2.free();
            }
        }
        return termBDDs.lastElement();
    }

    @Override
    public void classifyEffects(HashSet<String> addEffects,
                                HashSet<String> delEffects, Vector<Condition> condEffects, Vector<HashSet<String>> condEffectVars, boolean isNegated, boolean inCondEffect) {
        ListIterator<Expression> termsIt = terms.listIterator();
        while (termsIt.hasNext()) {
            termsIt.next()
                .classifyEffects(addEffects, delEffects, condEffects, condEffectVars, isNegated, inCondEffect);
        }
    }

    @Override
    public void getAllPredicates(Vector<Predicate> allPreds) {
        ListIterator<Expression> termIt = terms.listIterator();
        while (termIt.hasNext()) {
            termIt.next().getAllPredicates(allPreds);
        }
    }

    @Override
    public void findDelAdds(HashSet<String> delEffects,
            HashSet<String> addEffects, boolean isPositive) {
        ListIterator<Expression> termIt = terms.listIterator();
        while (termIt.hasNext()) {
            termIt.next().findDelAdds(delEffects, addEffects, isPositive);
        }
    }

    @Override
    public boolean eliminateDelEffects(HashSet<String> delEffectsToEliminate,
            boolean isPositive) {
        ListIterator<Expression> termIt = terms.listIterator();
        while (termIt.hasNext()) {
            if (termIt.next().eliminateDelEffects(delEffectsToEliminate,
                    isPositive)) {
                termIt.remove();
            }
        }
        return false;
    }

    @Override
    public String toString() {
        String ret;
        if (isAndTerm)
            ret = "(and\n";
        else
            ret = "(or\n";
        ListIterator<Expression> termsIt = terms.listIterator();
        while (termsIt.hasNext()) {
            ret += termsIt.next().toString() + "\n";
        }
        ret += ")";
        return ret;
    }

    public void setIsAndTerm(boolean isAndTerm) {
        this.isAndTerm = isAndTerm;
    }

    public boolean getIsAndTerm() {
        return isAndTerm;
    }

    public void setTerms(Vector<Expression> terms) {
        this.terms = terms;
    }

    public Vector<Expression> getTerms() {
        return terms;
    }

    public void createSyntaxTree(SyntaxTreeNode node, SyntaxTree tree, LinkedList<LinkedList<String>> partitions) {
        SyntaxTreeNode andOrNode = new SyntaxTreeNode();
        node.addSuccessor(andOrNode);
        ListIterator<Expression> termsIt = terms.listIterator();
        while (termsIt.hasNext()) {
            termsIt.next().createSyntaxTree(andOrNode, tree, partitions);
        }
    }

    /*public void splitConditionalEffect(LinkedList<LinkedList<String>> partitions) {
        ListIterator<Expression> termsIt = terms.listIterator();
        while (termsIt.hasNext()) {
            termsIt.next().splitConditionalEffect(partitions);
        }
    }

    public void splitEffect(LinkedList<LinkedList<String>> partitions) {
        ListIterator<Expression> termsIt = terms.listIterator();
        while (termsIt.hasNext()) {
            termsIt.next().splitEffect(partitions);
        }
        }*/

    private boolean isAndTerm;
    private Vector<Expression> terms;
}
