/*
 * SimpleGraph.h
 *
 *  Created on: 2013-04-14
 *      Author: sam
 */

#ifndef TESTGRAPH_H_
#define TESTGRAPH_H_

#include "core/Theory.h"
#include "Graph.h"
#include "DynDijkstra.h"
#include "core/SolverTypes.h"
#include "mtl/Map.h";
#include "MaxFlow.h"
namespace Minisat{
class DijGraph:public Graph,public Theory{
private:


	Lit False;
	Lit True;
	int local_q;

	Solver * S;
	DynamicGraph g;
	DynamicGraph antig;
	vec<Dijkstra*> reach_detectors;
	vec<Dijkstra*> non_reach_detectors;
	vec<vec<Lit> > reach_lits;

	vec<CRef> reach_markers;
	vec<CRef> non_reach_markers;
	Map<CRef,int> marker_map;
	vec<int> within;
	struct Edge{
		Var v;
		int from;
		int to;
	};
	vec<EdmondsKarp::Edge> cut;
	vec<vec<Edge> > edges;
	vec<Edge> edge_list;
	Var min_edge_var;
	int num_edges;
	EdmondsKarp mc;
public:
	DijGraph(Solver * S_):S(S_),mc(g){
		True = mkLit(S->newVar(),false);
			False=~True;
			S->addClause(True);
			num_edges=0;
			local_q=0;
	}
     ~DijGraph(){};
	 int newNode(){
		 edges.push();

		 antig.addNode();
		return g.addNode();
	}
	 void newNodes(int n){
		 for(int i = 0;i<n;i++)
			 newNode();
	 }
	int nNodes(){
		return g.nodes;
	}
	bool isNode(int n){
		return n>=0 && n<nNodes();
	}

	void backtrackUntil(int level){
		if(local_q>S->qhead)
			local_q=S->qhead;
	};
	void newDecisionLevel(){};

	void buildReason(Lit p, vec<Lit> & reason){
		CRef marker = S->reason(var(p));
		assert(marker != CRef_Undef);
		int d = marker_map[marker];
		reason.push(p);
		assert(d!=0);
		if(d>0){
			d--;
			Dijkstra & detector = *reach_detectors[d];
			//the reason is a path from s to p(provided by d)
			//p is the var for a reachability detector in dijkstra, and corresponds to a node
			Var v = var(p);
			int u =  v- var(reach_lits[d][0]);
			assert(detector.connected(u));

			while(int w= detector.previous(u) > -1){
				reason.push(mkLit( edges[w][u].v,true ));
				u=w;
			}

		}else{
			d=-d-1;
			Dijkstra & detector = *non_reach_detectors[d];
			//the reason is a cut separating p from s;
			//We want to find a min-cut in the full graph separating, where activated edges (ie, those still in antig) are weighted infinity, and all others are weighted 1.

			//This is a cut that describes a minimal set of edges which are disabled in the current graph, at least one of which would need to be activated in order for s to reach p
			//assign the mincut edge weights if they aren't already assigned.

			//set weights

			//compute the mincut
			Var v = var(p);
				int t =  v- var(reach_lits[d][0]);
				assert(!detector.connected(t));

			cut.clear();
			mc.minCut (detector.getSource(), t,cut);
			for(int i = 0;i<cut.size();i++){
				reason.push(mkLit( edges[cut[i].u][cut[i].v].v,false ));
			}
			/*for(int i = 0;i<g.nodes;i++){
				for(int j = 0;j<g.adjacency[i];j++){
					int v = g.adjacency[i][j];
					if(mc.parity[i]!=mc.parity[v]){
						//this edge is in the min-cut
						reason.push(mkLit( edges[i][v].v,true ));
					}
				}
			}*/
		}

	}
	void buildReachReason(int node,Dijkstra & d, bool negate,vec<Lit> & conflict){
		int u = node;
		while(int p = d.previous(u) != -1){
			Var e = min_edge_var+edges[u][p].v;
			conflict.push(mkLit(e, negate));
			u = p;
		}
	}
	void buildNonReachReason(int node, int detector ,vec<Lit> & conflict){
		int u = node;
		mc.minCut(non_reach_detectors[detector]->getSource(),node,cut);

		for(int i = 0;i<cut.size();i++){
			EdmondsKarp::Edge e = cut[i];
			conflict.push(mkLit( edges[e.u][e.v].v,false));
		}

	}
	bool propagateTheory(vec<Lit> & conflict){
		bool any_change = false;
		static vec<int> detectors_to_check;
		detectors_to_check.clear();
		while(local_q<S->qhead){
			Lit l = S->trail[local_q++];
			Var v = var(l);
			if(v>= min_edge_var && v<min_edge_var+num_edges){
				//this is an edge assignment
				int edge_num = v-min_edge_var;
				int from = edge_list[edge_num].from;
				int to = edge_list[edge_num].to;

				if (!sign(l)){
					g.addEdge(from,to);
					for(int i = 0;i<reach_detectors.size();i++){
						if(!reach_detectors[i]->marked && (reach_detectors[i]->connected_unsafe(from)||reach_detectors[i]->connected_unsafe(to))){
								detectors_to_check.push((i+1));
								reach_detectors[i]->marked =true;
							}
					}
				}else{
					antig.removeEdge(from,to);
					for(int i = 0;i<non_reach_detectors.size();i++){

						if(!non_reach_detectors[i]->marked && ( non_reach_detectors[i]->connected_unsafe(from)||non_reach_detectors[i]->connected_unsafe(to))){
							detectors_to_check.push(-(i+1));
							non_reach_detectors[i]->marked =true;
						}
					}
				}
			}

			for(int i = 0;i<detectors_to_check.size();i++){
				int d = detectors_to_check[i];
				assert(d!=0);
				if(d>0){
					d--;
					reach_detectors[d]->update();
					for(int j =0;j<reach_lits[d].size();j++){
						Lit l = reach_lits[d][j];
						if( reach_detectors[d]->connected(j)){
							if(S->value(l)==l_Undef){
								S->uncheckedEnqueue(l,reach_markers[d]) ;
							}else if (S->value(l)==l_False){
								//conflict
								//The reason is all the literals in the shortest path in to s in d
								conflict.push(l);
								buildReachReason(j,*reach_detectors[d],false,conflict);
								//add it to s
								//return it as a conflict
								return false;
							}
						}

					}
				}else{
					d=-d-1;
					non_reach_detectors[d]->update();
					for(int j =0;j<reach_lits[d].size();j++){
						Lit l = ~reach_lits[d][j];
						if(! non_reach_detectors[d]->connected(j)){
							if(S->value(l)==l_Undef){
								S->uncheckedEnqueue(l,non_reach_markers[d]) ;
							}else if (S->value(l)==l_False){
								//conflict
								//The reason is a cut separating s from t
								conflict.push(l);
								buildNonReachReason(j,d,conflict);
								//add it to s
								//return it as a conflict
								return false;
							}
						}

					}
				}
			}



		}

		//really simple dynamic optimization for online checking connectivity:
		//only need to do an update if an added edge has non-infinite endpoints in g, or if a removed edge has non-infinite endpoints in antig
		while(detectors_to_check.size()){

		}

		return true;
	};
	bool solve(vec<Lit> & conflict){return true;};



	Lit newEdge(int from,int to)
    {
		Var v = S->newVar();
		if(num_edges>0)
			assert(v==min_edge_var+num_edges);
		else
			min_edge_var=v;
		num_edges++;
		edge_list.push({v,from,to});
		//edges.push({from,to});
		edges[from].push({v,from,to});
		antig.addEdge(from,to);

    	return mkLit(v,false);
    }

	void reachesAny(int from, vec<Lit> & reaches,int within_steps=-1){
		assert(from<g.nodes);
		reach_markers.push(S->newReasonMarker());
		marker_map.insert(reach_markers.last(),reach_markers.size());

		non_reach_markers.push(S->newReasonMarker());
		//marker_map[non_reach_markers.last()]=-non_reach_markers.size();
		marker_map.insert(non_reach_markers.last(),non_reach_markers.size());

		reach_detectors.push(new Dijkstra(from,g));

		non_reach_detectors.push(new Dijkstra(from,antig));
		reach_lits.push();
		within.push(within_steps);
		for(int i = 0;i<g.nodes;i++){
			Var reachVar = S->newVar();
			Lit reachLit=mkLit(reachVar,false);
			reaches.push(reachLit);
			reach_lits.last().push(reachLit);
		}

    }

};

};

#endif /* TESTGRAPH_H_ */
