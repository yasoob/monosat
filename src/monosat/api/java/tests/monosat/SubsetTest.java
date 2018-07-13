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

import org.junit.Test;

import java.util.Arrays;
import java.util.Collections;

import static org.junit.Assert.*;

/**
 * Tests subset constraints
 */
public class SubsetTest {



  @Test
  public void test_Subset() {
    Solver solver = new Solver();
    Lit a = new Lit(solver);
    Lit b = new Lit(solver);
    Lit c = new Lit(solver);
    Lit result = Logic.xnor(a, b, c);
    assertTrue(solver.solve());

    Subset subset = new Subset(solver,Arrays.asList(a,b,c));
    Lit d = subset.atMost(Arrays.asList(a,b));
    assertTrue(solver.solve());
    solver.addClause(d);
    assertTrue(solver.solve());
    assertFalse(solver.solve(c));
    assertTrue(solver.solve(a));
    assertTrue(solver.solve(a.not(),b));
    assertTrue(solver.solve(a,b));
    assertFalse(solver.solve(a,b,c));

    solver.addClause(subset.atMost(Arrays.asList(a,c)));
    assertTrue(solver.solve());
    assertFalse(solver.solve(c));
    assertFalse(solver.solve(b));
    assertTrue(solver.solve(a));
    assertFalse(solver.solve(a.not(),b));
    assertTrue(solver.solve(a,b.not()));
    assertFalse(solver.solve(a,b));

  }
    @Test
    public void test_SubsetAMO() {
        Solver solver = new Solver();
        Lit a = new Lit(solver);
        Lit b = new Lit(solver);
        Lit c = new Lit(solver);
        Lit result = Logic.xnor(a, b, c);
        assertTrue(solver.solve());

        Subset subset = new Subset(solver,a,b,c);
        Lit d = subset.atMost(Arrays.asList(a,b));
        Logic.assertAtMostOne(a,b,c);
        assertTrue(solver.solve());
        solver.addClause(d);
        assertTrue(solver.solve());
        assertFalse(solver.solve(c));
        assertTrue(solver.solve(a));
        assertTrue(solver.solve(a.not(),b));
        assertTrue(solver.solve(a));
        assertTrue(solver.solve(b));
        assertFalse(solver.solve(a,b));
        assertFalse(solver.solve(a,b,c));

        solver.addClause(subset.atMost(Arrays.asList(a,c)));
        assertTrue(solver.solve());
        assertFalse(solver.solve(c));
        assertFalse(solver.solve(b));
        assertTrue(solver.solve(a));
        assertFalse(solver.solve(a.not(),b));
        assertTrue(solver.solve(a,b.not()));
        assertFalse(solver.solve(a,b));

    }


}
