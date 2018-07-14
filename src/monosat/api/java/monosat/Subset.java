/*
The MIT License (MIT)

Copyright (c) 2018, Sam Bayless

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*/

package monosat;

import java.nio.IntBuffer;
import java.util.*;
import java.util.stream.Collectors;

/**
 * Supports reasoning about subsets of a finite set of literals.
 * The intended use-case of this class is to assert that,
 * from among a set of literals, `atMost` some subset of those
 * literals may be true.
 *
 * This can be combined with clauses, pseudo-Boolean constraints,
 * and at-most-one constraints to provide more fully-featured capabilities.
 */
public final class Subset implements Iterable<Lit> {
  /** The solver instance this Subset belongs to. */
  private final Solver solver;
  /** A handle to this Subset in the native library. */
  private final long subsetPtr;

  private final List<Lit> lits;

  /**
   * Instantiate a new subset in solver.
   * A subset is a collection of literals, some or all of which may be true.
   * AtMost constraints allow the set of true literals from that set to be
   * conditionally restricted.
   * @param solver The solver instance in which to create this subset.
   * @param lits A collection of literals from which a subset will be chosen to be true.
   */
  public Subset(Solver solver, Collection<Lit> lits) {
    this.solver = solver;
    this.subsetPtr = MonosatJNI.newSubset(solver.getSolverPtr(),solver.getLitBuffer(lits),lits.size());
    this.lits = new ArrayList<>(lits);
  }

    /**
     * Instantiate a new subset in solver.
     * A subset is a collection of literals, some or all of which may be true.
     * AtMost constraints allow the set of true literals from that set to be
     * conditionally restricted.
     * @param solver The solver instance in which to create this subset.
     * @param lits A collection of literals from which a subset will be chosen to be true.
     */
    public Subset(Solver solver, Lit... lits) {
        this.solver = solver;
        this.subsetPtr = MonosatJNI.newSubset(solver.getSolverPtr(),solver.getLitBuffer(lits,0),lits.length);
        this.lits = new ArrayList<Lit>(Arrays.asList(lits));
    }

    /**
     * Get the nth literal from this subset
     * @param n The index of the literal to retrieve
     * @return The nth literal in the subset
     */
    Lit get(int n){
        return lits.get(n);
    }



  /**
   * Returns a literal that is true only if no literals in the subset outside of `lits` are true.
   * Does not require any of the literals in lits to be true.
   *
   * @param lits A collection of literals that belong to the subset, at most one of which may be true if the returned
   *             literal is true.
   * @return A literal that is true only if no literals in the subset but outside of `lits` are true.
   */
  Lit atMost(Collection<Lit> lits){
    return  solver.toLit(MonosatJNI.subsetAtMost(solver.getSolverPtr(), subsetPtr,solver.getLitBuffer(lits),
            lits.size()));
  }


    /**
     * Returns a literal that is true only if no literals in the subset outside of `lits` are true.
     * Does not require any of the literals in lits to be true.
     *
     * @param lits A collection of literals that belong to the subset, at most one of which may be true if the returned
     *             literal is true.
     * @return A literal that is true only if no literals in the subset but outside of `lits` are true.
     */
    Lit atMost(Lit... lits){
        return  solver.toLit(MonosatJNI.subsetAtMost(solver.getSolverPtr(), subsetPtr,solver.getLitBuffer(lits,0),
                lits.length));
    }

    @Override
    public Iterator<Lit> iterator() {
        return lits.iterator();
    }
}
