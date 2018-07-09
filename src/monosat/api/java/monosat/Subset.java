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
 */
public final class Subset {
  /** The solver instance this Subset belongs to. */
  private final Solver solver;
  /** A handle to this Subset in the native library. */
  private final long subsetPtr;

  /**
   * Instantiate a subset in solver.
   * A subset is a collection of literals, some or all of which may be true.
   * AtMost constraints allow the set of true literals from among the subset
   * to be conditionally restricted.
   *
   * @param solver The solver instance in which to create this subset.
   */
  public Subset(Solver solver, Collection<Lit> subset) {
    this.solver = solver;
    this.subsetPtr = MonosatJNI.newSubset(solver.getSolverPtr(),solver.getLitBuffer(subset),subset.size());
  }

  /**
   * Returns a literal that is true only if no literals in the subset but outside of `lits` are true.
   * This condition is one-sided; the returned literal does not need to be true if
   * some or all of the literals in 'lits' are true.
   * @param lits A collection of literals that belong to the subset, at most one of which may be true if the returned
   *             literal is true.
   * @return A literal that is true only if no literals in the subset but outside of `lits` are true.
   */
  Lit atMost(Collection<Lit> lits){
    return  solver.toLit(MonosatJNI.subsetAtMost(solver.getSolverPtr(), subsetPtr,solver.getLitBuffer(lits),
            lits.size()));
  }


}
