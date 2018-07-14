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

#ifndef SUBSETTHEORY_H_
#define SUBSETTHEORY_H_

#include "monosat/mtl/Vec.h"
#include "monosat/core/SolverTypes.h"
#include "monosat/core/Theory.h"
#include "monosat/core/Solver.h"

namespace Monosat {


//(Finite) Subset theory. This is a generalization of at-most-one constraints
class SubsetTheory: public Theory {
	Solver * S;
	int theory_index=-1;
	vec<bool> l_sign;
	int n_subset_vars=0;
	int n_vars = 0;
	struct AtMost{
		Lit cond=lit_Undef;
		LSet subset;
		bool in_at_mosts_to_prop=false;
	};
	LMap<AtMost*> at_mosts;
	vec<AtMost*> all_at_mosts;
	vec<Lit> possibly_true_or_unassigned_lits;
	vec<bool> is_possibly_true_or_unassigned;

	vec<Lit> possibly_unassigned_at_most_constraints;
	vec<bool> is_possibly_unassigned_atmost_constraint;
public:

	CRef assign_false_reason;
	//CRef assign_true_reason;

	LMap<Lit> litToTheory;
	LMap<Lit> litToSolver;
	vec<Lit> reasons;

	vec<Lit> tmp_clause;
	//If non undefined, this is a literal that is true when it should be false.
	Lit conflict_lit = lit_Undef;
	AtMost * conflict_atmost = nullptr;
	bool isSubsetVar(Var v){
		assert(v>=0);
		return v<n_subset_vars;
	}
	vec<AtMost*> at_mosts_to_prop;
	double propagationtime=0;
	int64_t stats_propagations=0;
	int64_t stats_lit_propagations=0;
	int64_t stats_propagations_skipped=0;
	int64_t stats_shrink_removed = 0;
	int64_t stats_reasons = 0;
	int64_t stats_conflicts = 0;
public:
    const char * getTheoryType()override{
		return "Subset";
	}
	SubsetTheory(Solver * S) :
			S(S) {
		S->addTheory(this);
		assign_false_reason=S->newReasonMarker(this);
		//assign_true_reason=S->newReasonMarker(this);

	}
	~SubsetTheory() {
	}

	Lit toSolver(Lit l){
		return litToSolver[l];
	}
	Lit toTheory(Lit l){
		return litToTheory[l];
	}

	void setLits(vec<Lit> & all_lits){
    	assert(litToTheory.size()==0);
		assert(n_vars==n_subset_vars);
		assert(n_subset_vars==0);
		for(Lit l:all_lits){
			if(litToTheory.has(l)){
				throw std::runtime_error("Cannot add the same lit twice to subset");
			}
			if(litToTheory.has(~l)){
				throw std::runtime_error("Cannot add both a lit and its negation to subset");
			}

			Var v = n_subset_vars;
			n_subset_vars++;
			n_vars++;

			l_sign.growTo(v+1,false);
			l_sign[v] = sign(l);
			S->newTheoryVar(var(l), getTheoryIndex(),v);
			litToTheory.insert(l,mkLit(v));
			litToSolver.insert(mkLit(v),l);

			is_possibly_true_or_unassigned.growTo(v+1,false);
			is_possibly_true_or_unassigned[v]=true;
			possibly_true_or_unassigned_lits.push(mkLit(v,l_sign[v]));

			reasons.growTo(v+1,lit_Undef);
		}
	}

	/**
	 * If cond is true, then at most the literals in 'lits' may be true (out of the literals in 'setLits').
	 * If cond is false, then nothing is implied.
	 * @param cond
	 * @param lits
	 */
	void addAtMostConstraint(Lit cond, vec<Lit> & lits){
		Var v = n_vars++;
		if(sign(cond)){
			throw std::runtime_error("Subset condition cannot be signed");
		}
		for(Lit l:lits){
			if(!litToTheory.has(l)){
				throw std::runtime_error("Subset literals must be in the set");
			}
		}
		S->newTheoryVar(var(cond), getTheoryIndex(),v);
		Lit p = mkLit(v);
		AtMost* atmost = new AtMost();
		atmost->cond = p;
		for(Lit t:lits) {
			Lit l = toTheory(t);
			atmost->subset.push(l);
		}
        litToTheory.insert(cond,p);
        litToSolver.insert(p,cond);
		at_mosts.insert(p,atmost);
        all_at_mosts.push(atmost);
		is_possibly_unassigned_atmost_constraint.growTo(v+1,false);
		is_possibly_unassigned_atmost_constraint[v]=true;
		possibly_unassigned_at_most_constraints.push(p);
    }


	inline int getTheoryIndex()const override {
		return theory_index;
	}
	inline void setTheoryIndex(int id) override {
		theory_index = id;
	}
	inline void newDecisionLevel() override {

	}
	inline void backtrackUntil(int untilLevel) override {

	}
	inline int decisionLevel() {
		return S->decisionLevel();
	}
	inline void undecideTheory(Lit l) override {
		if(isSubsetVar(var(l))) {
			if (l == conflict_lit) {
				conflict_lit = lit_Undef;
				conflict_atmost = nullptr;
			}
			if (!is_possibly_true_or_unassigned[var(l)]) {
				is_possibly_true_or_unassigned[var(l)] = true;
				possibly_true_or_unassigned_lits.push(mkLit(var(l),l_sign[var(l)]));
			}
			reasons[var(l)]=lit_Undef;
		}else{
			if(sign(l)){
				//do nothing - assigning an at most condition to false implies nothing
			}else {
				AtMost *atmost = at_mosts[l];
				if(atmost==conflict_atmost){
					conflict_lit = lit_Undef;
					conflict_atmost = nullptr;
				}
			}
		}
	}
	void enqueueTheory(Lit l) override {
		if(conflict_lit==lit_Undef){
			assert(conflict_atmost==nullptr);
			if(isSubsetVar(var(l))){

				if (sign(l)==l_sign[var(l)]){
					//if we assign l to true, that implies that any at most set that l is not a member of is false
					//(though it does _not_ imply that any at most set is true, because they are one sided)
					//do nothing, for now
				}else{
					//it is always safe to assign a lit to false.
				}
			}else{
				if(sign(l)){
					//do nothing - assigning an at most condition to false implies nothing
				}else{
					AtMost * atmost = at_mosts[l];
					assert(atmost);
					if(!atmost->in_at_mosts_to_prop) {
						atmost->in_at_mosts_to_prop=true;
						at_mosts_to_prop.push(atmost);
					}
				}
			}
		}else{
			//the theory is in conflict, do nothing
		}
	}
	;
	bool propagateTheory(vec<Lit> & conflict) override {
		S->theoryPropagated(this);

		if (conflict_lit==lit_Undef){
			stats_propagations++;

			while(at_mosts_to_prop.size()){
				AtMost * atmost = at_mosts_to_prop.last();
				Lit p = atmost->cond;
				if(S->value(toSolver(p))==l_True) {
					LSet &lits = atmost->subset;
					//enforce this at most constraint
					int j = 0;
					int i = 0;
					for (; i < possibly_true_or_unassigned_lits.size(); i++) {
						Lit p = possibly_true_or_unassigned_lits[i];
						assert(p != lit_Undef);
						assert(is_possibly_true_or_unassigned[var(p)]);
						lbool val = S->value(toSolver(p));
						if (val == l_True) {
							if (!lits.contains(p)) {
								conflict_lit = p;
								conflict_atmost = atmost;
								//this is a conflict, so don't remove this literal from possibly unassigned
								//keep the remaining literals in this set
								for (; i < possibly_true_or_unassigned_lits.size(); i++) {
									possibly_true_or_unassigned_lits[j++] = possibly_true_or_unassigned_lits[i];
								}
								break;
							}
							//literal is true, so leave it in 'true or unassigned'
							possibly_true_or_unassigned_lits[j++] = p;
						} else if (val == l_False) {
							//drop this literal
							is_possibly_true_or_unassigned[var(p)] = false;

						} else {
							//literal is unassigned
							possibly_true_or_unassigned_lits[j++] = p;
							if(!lits.contains(p)){
								//assign this literal to false
								stats_propagations++;
								assert(reasons[var(p)]==lit_Undef);
								reasons[var(p)]=atmost->cond;

								S->enqueue(~toSolver(p),assign_false_reason);


							}
						}
					}

					possibly_true_or_unassigned_lits.shrink(i - j);
				}
				if(conflict_lit!=lit_Undef){
					break;
				}else {
					at_mosts_to_prop.pop();
					atmost->in_at_mosts_to_prop = false;
				}
			}

		}
		if(conflict_lit!=lit_Undef){
			assert(conflict_atmost!=nullptr);
			conflict.clear();
			assert(!conflict_atmost->subset.contains(conflict_lit));
			//at least one of these must be false
			conflict.push(~toSolver(conflict_lit));
			conflict.push(~toSolver(conflict_atmost->cond));

			stats_conflicts++;
			return false;
		}
		return true;
	}
	void printStats(int detailLevel) override {

		printf("Subset Theory %d stats:\n", this->getTheoryIndex());

		printf("Propagations: %" PRId64 " (%f s, avg: %f s, %" PRId64 " skipped,  %" PRId64 " lits)\n", stats_propagations, propagationtime,
			   (propagationtime) / ((double) stats_propagations + 1), stats_propagations_skipped, stats_lit_propagations);

		printf("Conflicts: %" PRId64 "\n", stats_conflicts);
		printf("Reasons: %" PRId64 "\n", stats_reasons);

		fflush(stdout);

	}

	inline bool solveTheory(vec<Lit> & conflict) override {
		return propagateTheory(conflict);
	}
	inline void buildReason(Lit p, vec<Lit> & reason, CRef reason_marker) override {
		stats_reasons++;
		assert(reason_marker==assign_false_reason);
		if(isSubsetVar(var(p))){
			assert(reasons[var(p)]!=lit_Undef);
			assert(sign(p));
			assert(S->value(toSolver(p))==l_True);

			reason.push(toSolver(p));
			Lit r = reasons[var(p)];
			reason.push(~toSolver(r));

		}else{
			assert(false);
		}
	}
	bool check_solved() override {
		int n_true=0;
		for (AtMost * atmost:all_at_mosts){
			lbool val = S->value(toSolver(atmost->cond));
			if(val!=l_True){
				continue;//false at most constraints are always satisfied
			}
			for(int v = 0;v<n_subset_vars;v++){
				Lit l = mkLit(v, l_sign[v]);
				if(atmost->subset.contains(l)){
					//do nothing
				}else{
					if(S->value(toSolver(l))==l_True){
						return false;
					}
				}
			}
		}

		return true;
	}
private:


};

}
;

#endif /* AMOTheory_H_ */
