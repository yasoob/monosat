/*
 * MaxFlow.h
 *
 *  Created on: 2013-05-30
 *      Author: sam
 */

#ifndef MAXFLOW_H_
#define MAXFLOW_H_


#include "mtl/Vec.h"
#include "mtl/Heap.h"
#include "DynDijkstra.h"
#include <set>
//adapted from http://www.boost.org/doc/libs/1_46_1/boost/graph/stoer_wagner_min_cut.hpp
using namespace Minisat;
//Finds a global min-weight-cut, over all possible s-t, NOT the expected normal s-t min-cut
class MinCut{

  	//  vec<vec<int> > & g ;


  	 // int nodes;
  	  //vec<vec<int> >& adj;
  	  DynamicGraph & g;
  	  vec<int> assignments;
  	  vec<vec<float> > weight;//this is a full edge matrix

  //	  vec<vec<float> > cur_weight;//this is a full edge matrix
  	  vec<float> keys;
  	  vec<bool> parity;
/*  	  struct Edge{
  		  int u;
  		  int v;
  		  float weight;
  	  };
  	  vec<Edge> edges;*/
  /*	 struct Comp {
  		const vec<vec<float> >& _cur_weight;
  		        bool operator () (int x, int y) const {
  		        	assert(_cur_weight.size()==_cur_weight[0].size());
  		        	int xa = x/_cur_weight.size();
  		        	int xb = x%_cur_weight.size();
  		        	int ya = y/_cur_weight.size();
					int yb = y%_cur_weight.size();
  		        	return _cur_weight[xa][xb] > _cur_weight[ya][yb]; }
  		      Comp(const vec<vec<float> > & cw) : _cur_weight(cw) { }
  	  	  };*/
 	 struct Comp {
   		const vec<float> & _keys;
   		        bool operator () (int x, int y) const {
   		        	return _keys[x]>_keys[y];
   		        }
   		      Comp(const vec<float> & k) : _keys(k) { }
   	  	  };
	  Heap<Comp> pq;
  	//std::set<int> assignedVertices;
	  vec<int> assignedVertices;


    /**
     * \brief Performs a phase of the Stoer-Wagner min-cut algorithm
     *
     * Performs a phase of the Stoer-Wagner min-cut algorithm.
     *
     * As described by Stoer & Wagner (1997), a phase is simply a maximum adjacency search
     * (also called a maximum cardinality search), which results in the selection of two vertices
     * \em s and \em t, and, as a side product, a minimum <em>s</em>-<em>t</em> cut of
     * the input graph. Here, the input graph is basically \p g, but some vertices are virtually
     * assigned to others as a way of viewing \p g as a graph with some sets of
     * vertices merged together.
     *
     * This implementation is a translation of pseudocode by Professor Uri Zwick,
     * School of Computer Science, Tel Aviv University.
     *
     * \pre \p g is a connected, undirected graph
     * \param[in] g the input graph
     * \param[in] assignments a read/write property map from each vertex to the vertex that it is assigned to
     * \param[in] assignedVertices a list of vertices that are assigned to others
     * \param[in] weights a readable property map from each edge to its weight (a non-negative value)
     * \param[out] pq a keyed, updatable max-priority queue
     * \returns a tuple (\em s, \em t, \em w) of the "<em>s</em>" and "<em>t</em>"
     *     of the minimum <em>s</em>-<em>t</em> cut and the cut weight \em w
     *     of the minimum <em>s</em>-<em>t</em> cut.
     * \see http://www.cs.tau.ac.il/~zwick/grad-algo-08/gmc.pdf
     *
     * \author Daniel Trebbien
     * \date 2010-09-11
     */


    void stoer_wagner_phase( int & s, int & t, float & w ) {


      assert(pq.empty());

      for(int v = 0;v<g.nodes;v++){
    	  if (v ==assignments[v]) {
    		  keys[v]=0;
    		  pq.update(v);

    	  }
      }


      assert(pq.size() >= 2);

       s = -1;
       t =-1;

      while (!pq.empty()) { // while PQ \neq {} do
        int u = pq.removeMin(); // u = extractmax(PQ)
        w = keys[u];

        s = t; t = u;


        	for(int j = 0;j<g.adjacency[u].size();j++){
        		int q = g.adjacency[u][j];
        		int v = assignments[q];
        		if(pq.inHeap(v)){

        			keys[v]+=weight[u][q];//        put(keys, v, get(keys, v) + get(weights, e)); // increasekey(PQ, v, wA(v) + w(u, v))
        			pq.decrease(v);
        		}
        	}


        	for (int i = 0;i<assignedVertices.size();i++) {
			  int uPrime = assignedVertices[i];
			  if(assignments[uPrime]==u){
				  for(int j = 0;j<g.adjacency[uPrime].size();j++){
					 int q = g.adjacency[uPrime][j];
					 int v = assignments[q];
					 if(pq.inHeap(v)){
						 keys[v]+=weight[u][q];
						 pq.decrease(v);
					 }
				  }
			  }

		  }
        //	assignedVertices.clear();
      }
    }


public:
 	MinCut(DynamicGraph & graph):g(graph),pq(Comp(keys)){
 		  weight.growTo(g.nodes);
 				   weight.shrink(weight.size()-g.nodes);
 					  for(int v= 0 ;v<g.nodes;v++){
 						  weight[v].growTo(g.nodes);
 						  weight[v].shrink(weight[v].size()-g.nodes);
 						  for(int w = 0;w<g.nodes;w++){
 							weight[v][w]=0;
 						  }
 					  }
 					  initEdgeWeights(1);
  	}
    /**
     * \brief Computes a min-cut of the input graph
     *
     * Computes a min-cut of the input graph using the Stoer-Wagner algorithm.
     *
     * \pre \p g is a connected, undirected graph
     * \pre <code>pq.empty()</code>
     * \param[in] g the input graph
     * \param[in] weights a readable property map from each edge to its weight (a non-negative value)
     * \param[out] parities a writable property map from each vertex to a bool type object for
     *     distinguishing the two vertex sets of the min-cut
     * \param[out] assignments a read/write property map from each vertex to a \c vertex_descriptor object. This
     *     map serves as work space, and no particular meaning should be derived from property values
     *     after completion of the algorithm.
     * \param[out] pq a keyed, updatable max-priority queue
     * \returns the cut weight of the min-cut
     * \see http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.114.6687&rep=rep1&type=pdf
     * \see http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.31.614&rep=rep1&type=pdf
     *
     * \author Daniel Trebbien
     * \date 2010-09-11
     */
   float stoer_wagner_min_cut( int &s, int& t) {



	   int n = g.nodes;
	   //full edge matrix
	   /*cur_weight.growTo(g.nodes);
	   cur_weight.shrink(cur_weight.size()-g.nodes);
	      for(int v= 0 ;v<g.nodes;v++){
	    	  cur_weight[v].growTo(g.nodes);
	      	  cur_weight[v].shrink(cur_weight[v].size()-g.nodes);
	      	  for(int w = 0;w<g.nodes;w++){
	      		cur_weight[v][w]=0;
	      	  }
	      }*/


	   keys.growTo(g.nodes);
	   parity.growTo(g.nodes);
      // initialize `assignments` (all vertices are initially assigned to themselves)
      assignments.growTo(g.nodes);
      for(int v= 0 ;v<g.nodes;v++)
    	  assignments[v]=v;


      float bestW;

     stoer_wagner_phase(s, t, bestW);
      assert(s != t);
      for(int v=0;v<g.nodes;v++)
    	  parity[v]=v==t?1:0;

      assignments[t]=s;
      assignedVertices.push(t);
      --n;

      for (; n >= 2; --n) {
        float w;
        stoer_wagner_phase(s, t, w);
        assert(s != t);

        if (w < bestW) {
        	for(int v = 0;v<g.nodes;v++){
        		parity[v]=assignments[v]==t?1:0;
        		if(assignments[v]==t)// all vertices that were assigned to t are now assigned to s
        			assignments[v]=s;
        	}
          bestW = w;
        } else {
        	for(int v = 0;v<g.nodes;v++){
        		if(assignments[v]==t)
        			assignments[v]=s;// all vertices that were assigned to t are now assigned to s

        	}
        }
        if(assignments[t]==t)
        	assignedVertices.push(t);
        assignments[t]=s;

      }

      assert(pq.empty());

      return bestW;
    }

   void setWeight(int from, int to, float w){
	   if(from>=weight.size() || to>=weight.size()){
		   weight.growTo(g.nodes);
		   weight.shrink(weight.size()-g.nodes);
			  for(int v= 0 ;v<g.nodes;v++){
				  weight[v].growTo(g.nodes);
				  weight[v].shrink(weight[v].size()-g.nodes);
				  for(int w = 0;w<g.nodes;w++){
					weight[v][w]=0;
				  }
			  }
	   }
	   weight[from][to]=w;
   }
   void zeroAllWeights(){
	   for(int i = 0;i<weight.size();i++){
			   for(int j = 0;j<weight[i].size();j++){

				   weight[i][j]=0;
			   }
		   }
   }
   void initEdgeWeights(float w){
	zeroAllWeights();
	   for(int i = 0;i<g.adjacency.size();i++){
		   for(int j = 0;j<g.adjacency[i].size();j++){
			   int w = g.adjacency[i][j];
			   setWeight(i,w,1);
		   }
	   }
   }
   //Return which of the two partitions (true or false) this node is in
   bool getPartition(int node){
	   return parity[node];
   }
};
#endif /* MAXFLOW_H_ */