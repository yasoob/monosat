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

#ifndef BV_SUBSETTHEORY_H_
#define BV_SUBSETTHEORY_H_

#include "monosat/mtl/Vec.h"
#include "monosat/core/SolverTypes.h"
#include "monosat/core/Theory.h"
#include "monosat/core/Solver.h"
#include "monosat/bv/BVTheorySolver.h"

namespace Monosat {


//(Finite) Set theory for bitvectors.
template<typename Weight>
class BVSetTheory: public Theory {
	Solver * S;
	int theory_index=-1;
	vec<bool> l_sign;
	int n_subset_vars=0;
    class BVSets;
    BVTheorySolver<Weight> * bv;
    /**
     * If cond is true, then this bitvector must be
     * one of these values. If cond is false, then this
     * bitvector must not be one of these values.
     */
    struct BVSet{
        BVSets * belongsTo;
        Lit cond=lit_Undef;
        IntSet<Weight> values;
        vec<bool> equivalent_bits;//true for the indexes of bits that are equal in all values
        vec<BVSet*> mutuallyExclusiveSets;
        vec<BVSet*> impliedSets;
        BVSet(BVSets * outer, Lit cond, const IntSet<Weight> & vals):belongsTo(outer),cond(cond){
            values.insertAll(vals.toVec());
        }
        int getWidth(){
            return belongsTo->bvwidth;
        }
        int getBV(){
        	return belongsTo->bvID;
        }
        bool hasValue(Weight val){
            return values.contains(val);
        }
        bool anyValsInCommon(BVSet * other){
            if(other->values.size()<values.size()){
                return other->anyValsInCommon(this);
            }else {
                for (Weight &v:values) {
                    if(other->values.contains(v)){
                        return true;
                    }
                }
                return false;
            }
        }
        bool allValsContainedIn(BVSet * other){
            for (Weight &v:values) {
                if(!other->values.contains(v)){
                    return false;
                }
            }
            return true;
        }
    };
    struct BVSets {
        int bvID;
		int bvwidth;
        BVTheorySolver<Weight> * bv;
        BVSets(int bvID){
            this->bvID = bvID;
        }


        vec<BVSet*> sets;

        int getBV(){
        	return bvID;
        }

        BVSet* getSet(IntSet<Weight> & find){
			//is there a better option here than a linear search?
			for(BVSet * set:sets){
				if(set->values.equals(find)){
					return set;
				}
			}
			return nullptr;
        }

        BVSet * newSet(Lit l, IntSet<Weight> & vals){
            assert(vals.size()>0);
			BVSet * set = new BVSet(this,l,vals);
            set->equivalent_bits.growTo(bvwidth,false);
			//todo: vectorize this for ints/longs
            for(int i = 0;i<bvwidth;i++){
                bool allBitsTrue = true;
                bool allBitsFalse = true;
                for(int val:vals){
                    bool b = bv->getBitFromConst(val, i);
                    allBitsTrue &= b;
                    allBitsFalse &= !b;
                }
                if (allBitsTrue|| allBitsFalse){
                    set->equivalent_bits[i]=true;
                }
            }
            sets.push(set);
            return set;
        }


    };

	LMap<BVSet*> conditional_map;
    LMap<int> bv_map;
    IntSet<Var> bvvars;
	vec<BVSet*> all_sets;

	vec<BVSets*> bv_sets;


public:

	CRef assign_false_reason;
	CRef assign_true_reason;

	vec<Lit> reasons;

	vec<Lit> tmp_clause;
	//If non undefined, this is a literal that is true when it should be false.
	Lit conflict_lit = lit_Undef;
	BVSet * conflict_BVSet = nullptr;

	vec<BVSet*> at_mosts_to_prop;
	int64_t stats_propagations=0;
	int64_t stats_reasons = 0;
	int64_t stats_conflicts = 0;
public:
    const char * getTheoryType()override{
		return "BVSet";
	}
	BVSetTheory(Solver * S, BVTheorySolver<Weight> * bv) :
			S(S) {
		S->addTheory(this);
        this->bv = bv;
		assign_false_reason=S->newReasonMarker(this);
	}
	~BVSetTheory() {
	}
    Lit newSet(int bvID,const vec<Weight> & vals){
        IntSet<Weight> uniqueVals;
        uniqueVals.insertAll(vals);
        return newSet(bvID,uniqueVals);
    }
	Lit newSet(int bvID, IntSet<Weight> & vals){
		/**
		 * If this bv overlaps with any other sets, then combine them
		 * If it _doesn't_ overlap at all with any other sets, then
		 * we know that they are mutually exclusive.
		 * If this exact bv and set exist already, return their existing literal
		 */

        BVSets & sets = getSets(bvID);
		BVSet * set =sets.getSet(vals);
        if(set){
            return set->cond;
        }
        if(vals.size()==0){
            return ~S->True();
        }else {
            Lit solverLit = mkLit(S->newVar());
            Lit l = mkLit(S->newTheoryVar(var(solverLit), getTheoryIndex(), var(solverLit)));
            set = sets.newSet(l, vals);
            conditional_map.insert(l,set,nullptr);

            return set->cond;
        }
    }
private:
    vec<int> all_bvs;
    IntSet<int> bvIDsToProp;
    BVSets & getSets(int bvID){
        bv_sets.growTo(bvID+1,nullptr);
        if(bv_sets[bvID]==nullptr){
            all_bvs.push(bvID);
            bv_sets[bvID] = new BVSets(bvID);
            bv_sets[bvID]->bvwidth = bv->getWidth(bvID);
            bv_sets[bvID]->bv = bv;
            for(Lit b:bv->getBV(bvID).getBits()){
                Lit outer = bv->toSolver(b);
                S->setTheoryVar(var(outer),getTheoryIndex(),var(b));
                bv_map.insert(b, bvID,-1);
                bvvars.insert(var(b));
            }
            bvIDsToProp.insert(bvID);
        }
        return *bv_sets[bvID];
    }
public:

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

	}
    bool bvHasSet(int bvID){
        return all_sets.size()>bvID && all_sets[bvID]!=nullptr;
    }
    bool isConditional(Lit l){
        return (conditional_map.has(l) && conditional_map[l]) ||
			   (conditional_map.has(~l)&& conditional_map[~l]);
    }
    BVSet * getSetFromConditional(Lit l){
        if(conditional_map.has(l) && conditional_map[l]){
            return conditional_map[l];
        }else if(conditional_map.has(~l) && conditional_map[~l]){
			return conditional_map[~l];
		}else{
        	throw new std::runtime_error("No such conditional");
        }
    }
	BVSets * getSetsFromBVLit(Lit l){
		if(bv_map.has(l) && bv_map[l]>=0){
			return bv_sets[bv_map[l]];
		}else if(bv_map.has(~l) && bv_map[~l]>=0){
			return bv_sets[bv_map[~l]];
		}else{
			throw new std::runtime_error("No such bvset");
		}
	}
    bool isBVLit(Lit l){
        return bvvars.contains(var(l));
    }
	void enqueueTheory(Lit l) override {
        if(isConditional(l)){
			BVSet * set = getSetFromConditional(l);
			bvIDsToProp.insert(set->getBV());
        }else if (isBVLit(l)){
			BVSets * sets = getSetsFromBVLit(l);
			bvIDsToProp.insert(sets->getBV());
        }else{
            throw new std::runtime_error("Unknown literal");
        }
	}

	Lit toSolver(Lit l){
        if(isBVLit(l)){
            return bv->toSolver(l);
        }else {
            return l;
        }
    }

    lbool value(Lit l){
        if(isBVLit(l)){
            return bv->value(l);
        }else {
            return S->value(toSolver(l));
        }
    }

    LSet diffs;

    bool findDiffs(BVSet * set,LSet &  diffs){
        int width = set->getWidth();
        int bvID = set->getBV();
        vec<Lit> & bits = bv->getBits(bvID);
        bool anyValsIncluded = false;
        for(Weight & val:set->values){
            bool valInSet = true;
            for(int i = 0;i<width;i++){
                Lit bit = bits[i];
                lbool v = value(bit);
                if(v==l_Undef){
                    continue;
                }
                bool expected = bv->getBitFromConst(val, i);
                if(v==l_True != expected) {
                    valInSet= false;
                    // todo: Instead of picking the lowest bit to be the representative differing bit,
                    // we could try to find a minimal set of differing bits
                    if(v==l_True) {
                        diffs.insert(bit);
                    }else{
                        diffs.insert(~bit);
                    }
                    break;
                }
            }
            if(valInSet){
                anyValsIncluded = true;
                break;
            }
        }
        return anyValsIncluded;
    }

	bool propagateBV(int bvID, vec<Lit> & conflict){
        stats_propagations++;
	    diffs.clear();
        BVSets & sets = getSets(bvID);
        int width = sets.bvwidth;
        vec<Lit> & bits = bv->getBits(bvID);
        for(BVSet * set:sets.sets){
            Lit cond = set->cond;
            bool anyValsIncluded=false;
            bool allNonEquivalentBitsSet = true;
            for(int i = 0;i<width;i++) {
                lbool v = value(bits[i]);
                if(!set->equivalent_bits[i]) {
                    if (v == l_Undef) {
                        allNonEquivalentBitsSet = false;
                    }
                }
            }
            anyValsIncluded = findDiffs(set,diffs);

            if(value(cond)==l_True){
                if(!anyValsIncluded){
                    conflict.push(toSolver(~cond));
                    // the reason why no values are included is a subset of the literals, such that
                    // for each value in values, one differing bit is represented.
                    for(Lit l:diffs){
                        assert(value(l)==l_True);
                        conflict.push(toSolver(~l));
                    }
                    stats_conflicts++;
                    return false;
                }
            }else if(value(cond)==l_False){
                if(allNonEquivalentBitsSet && anyValsIncluded){
                    //the reason for the conflict is that the bv equals one of the values exactly.
                    //we can remove any bits that match all other values. The set of such bits can be computed
                    //once per set
                    conflict.push(toSolver(cond));
                    for(int i = 0;i<width;i++){
                        if(!set->equivalent_bits[i]){
                            Lit l = bits[i];
                            if(value(l)==l_True) {
                                conflict.push(toSolver(~l));
                            }else{
                                conflict.push(toSolver(l));
                            }
                        }
                    }
                    stats_conflicts++;
                    return false;
                }
            }else if (allNonEquivalentBitsSet){

                if(anyValsIncluded){
                    S->enqueue(toSolver(cond),assign_true_reason);

                }else{
                    S->enqueue(~toSolver(cond),assign_false_reason);
                }
            }
        }
        return true;
    }

	bool propagateTheory(vec<Lit> & conflict) override {
		S->theoryPropagated(this);
		for(int bvID:bvIDsToProp){
            if(!propagateBV(bvID,conflict)){
                return false;
            }
		}
        bvIDsToProp.clear();
		return true;
	}
	void printStats(int detailLevel) override {
        printf("BVSet Theory %d stats:\n", this->getTheoryIndex());
        printf("Propagations: %" PRId64 "\n",stats_propagations);
        printf("Conflicts: %" PRId64 "\n", stats_conflicts);
        printf("Reasons: %" PRId64 "\n", stats_reasons);
        fflush(stdout);
	}

	inline bool solveTheory(vec<Lit> & conflict) override {
		return propagateTheory(conflict);
	}
	inline void buildReason(Lit p, vec<Lit> & reason, CRef reason_marker) override {
        stats_reasons++;
        assert(value(p)==l_True);
        if(conditional_map.has(p) && conditional_map[p]){
            BVSet * set = conditional_map[p];
            assert(reason_marker==assign_true_reason);
            assert(p==set->cond);
            reason.push(toSolver(set->cond));
            diffs.clear();
            findDiffs(set,diffs);
            // the reason why no values are included is a subset of the literals, such that
            // for each value in values, one differing bit is represented.
            for(Lit l:diffs){
                assert(value(l)==l_True);
                reason.push(toSolver(~l));
            }
        }else if (conditional_map.has(~p) && conditional_map[~p]){
            BVSet * set = conditional_map[~p];
            assert(p==~set->cond);
            int width = set->getWidth();
            int bvID = set->getBV();
            vec<Lit> & bits = bv->getBits(bvID);
            assert(reason_marker==assign_false_reason);
            reason.push(~toSolver(set->cond));
            for(int i = 0;i<width;i++){
                if(!set->equivalent_bits[i]){
                    Lit l = bits[i];
                    if(value(l)==l_True) {
                        reason.push(toSolver(~l));
                    }else{
                        reason.push(toSolver(l));
                    }
                }
            }
        }else{
            throw std::runtime_error("Bad reason");
        }
	}
	bool check_solved() override {
        for(int bvID:all_bvs){
            BVSets & sets = getSets(bvID);
            for(BVSet * set:sets.sets){
                Lit cond = set->cond;
                lbool val = value(cond);
                bool anyContained = false;
                for(Weight val:set->values){
                    if(val<=bv->getOverApprox(bvID) && val>=bv->getUnderApprox(bvID)){
                        anyContained=true;
                        break;
                    }
                }

                if(val==l_True && !anyContained){
                    return false;
                }else if (val==l_False && anyContained){
                    return false;
                }
            }
        }
		return true;
	}
    struct SetContainmentLT{

        bool operator ()(BVSet* x, BVSet* y) const {
            if(x->allValsContainedIn(y)){
                //x is smaller than y
                return false;
            }else{
                //either y is smaller than x, or they are incomparable.
                if(y->allValsContainedIn(x)) {
                    return true;
                }else{
                    return x->values.size() <= y->values.size();
                }
            }
        }
        SetContainmentLT(){
        }
    };
	void preprocess() override{
        //todo: build trees of containing sets, find mutually exclusive sets and comparisons.
        sort(all_bvs);
        for(int bvID:all_bvs){
            BVSets & sets = getSets(bvID);
            //find all relevant comparisons/equalities
            for(Weight & to:bv->getConstantEqualities(bvID)){
                Lit l = bv->getConstantEquality(bvID, to);
                for(BVSet * set:sets.sets){
                    Lit cond = toSolver(set->cond);
                    if(set->hasValue(to)){
                        //if this set is true, then this equality comparison must also be true
                        S->addClause(l,~cond);
                        S->addClause(~l,cond);
                    }else{
                        //if this set is true, then this equality comparison must be false
                        S->addClause(l,cond);
                        S->addClause(~l,~cond);
                    }
                }
            }
            for(int i =0;i<sets.sets.size();i++){
                BVSet * set1 = sets.sets[i];
                Lit cond1 = toSolver(set1->cond);
                for(int j = i+1;j<sets.sets.size();j++){
                    BVSet * set2 = sets.sets[j];
                    Lit cond2 = toSolver(set2->cond);
                    if(set1->anyValsInCommon(set2)){
                        if(set1->allValsContainedIn(set2)){
                            set2->impliedSets.push(set1);
                            //if set1 is true, then set2 must also be true
                            S->addClause(~cond1,cond2);
                        }else if (set2->allValsContainedIn(set1)){
                            set1->impliedSets.push(set2);
                            S->addClause(~cond2,cond1);
                        }
                    }else{
                        set1->mutuallyExclusiveSets.push(set2);
                        set2->mutuallyExclusiveSets.push(set1);
                        //if set1 is true, set2 is false, and vice versa
                        S->addClause(cond1,cond2);
                        S->addClause(~cond1,~cond2);
                    }
                }
            }

            //sort sets into partial order
            sort(sets.sets,SetContainmentLT());
        }
    }
private:


};

}
;

#endif /* AMOTheory_H_ */