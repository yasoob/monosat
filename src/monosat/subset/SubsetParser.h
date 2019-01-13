/**************************************************************************************************
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
 **************************************************************************************************/

#ifndef SUBSET_PARSER_H_
#define SUBSET_PARSER_H_

#include <cstdio>

#include "monosat/utils/ParseUtils.h"
#include "monosat/core/SolverTypes.h"

#include "monosat/core/Config.h"
#include "monosat/core/Dimacs.h"
#include <set>
#include <string>
#include <sstream>
#include "monosat/subset/SubsetTheory.h"

namespace Monosat {


//=================================================================================================
// GRAPH Parser:
template<class B, class Solver>
class SubsetParser : public Parser<B, Solver> {
    using Parser<B, Solver>::mapVar;

    struct AtMost {

        Lit cond = lit_Undef;
        vec<Lit> lits;
    };

    struct Subset {
        int id = -1;
        vec<Lit> lits;
        vec<AtMost> at_mosts;
    };

    vec<Subset*> subsets;


public:
    SubsetParser() : Parser<B, Solver>("Subset"){

    }

    bool parseLine(B& in, Solver& S){

        skipWhitespace(in);
        if(*in == EOF)
            return false;
        if(match(in, "subset atmost")){
            int subset_id = parseInt(in);
            assert(subset_id >= 0);
            subsets.growTo(subset_id + 1, nullptr);
            if(subsets[subset_id] == nullptr){
                subsets[subset_id] = new Subset();
            }
            subsets[subset_id]->at_mosts.push();
            AtMost& atmost = subsets[subset_id]->at_mosts.last();
            {
                int parsed_lit = parseInt(in);
                bool sign = false;
                assert (parsed_lit != 0);

                if(parsed_lit < 0){
                    sign = true;
                    parsed_lit = -parsed_lit;
                    assert(false);
                }
                assert(parsed_lit > 0);
                Var var = parsed_lit - 1;
                var = mapVar(S, var);
                atmost.cond = mkLit(var, sign);
            }

            for(;;){
                int parsed_lit = parseInt(in);
                bool sign = false;
                if(parsed_lit == 0)
                    break;
                if(parsed_lit < 0){
                    sign = true;
                    parsed_lit = -parsed_lit;
                }
                assert(parsed_lit > 0);
                Var var = parsed_lit - 1;
                var = mapVar(S, var);
                atmost.lits.push(mkLit(var, sign));
            }

            return true;
        }else if(match(in, "subset")){
            //read in subset constraints the same way as clauses, except that all ints are interpreted as variables, not lits, for now:
            int subset_id = parseInt(in);
            assert(subset_id >= 0);
            subsets.growTo(subset_id + 1, nullptr);
            if(subsets[subset_id] == nullptr){
                subsets[subset_id] = new Subset();
            }else{
                assert(subsets[subset_id]->lits.size() == 0);
            }

            for(;;){
                int parsed_lit = parseInt(in);
                bool sign = false;
                if(parsed_lit == 0)
                    break;
                if(parsed_lit < 0){
                    sign = true;
                    parsed_lit = -parsed_lit;
                }
                assert(parsed_lit > 0);
                Var var = parsed_lit - 1;
                var = mapVar(S, var);
                subsets[subset_id]->lits.push(mkLit(var, sign));

            }

            return true;
        }

        return false;
    }

    void implementConstraints(Solver& S){
        for(Subset* subset:subsets){
            if(subset != nullptr){
                SubsetTheory* theory = new SubsetTheory(&S);
                theory->setLits(subset->lits);
                for(AtMost& atmost:subset->at_mosts){
                    theory->addAtMostConstraint(atmost.cond, atmost.lits);
                }
            }
        }
    }


};

//=================================================================================================
};

#endif /* GRAPH_PARSER_H_ */
