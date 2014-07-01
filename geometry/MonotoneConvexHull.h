/*
 * SimpleConvexHull.h
 *
 *  Created on: 2014-02-23
 *      Author: sam
 */


#ifndef MONOTONE_CONVEXHULL_H_
#define MONOTONE_CONVEXHULL_H_
#include "ConvexHull.h"
#include "PointSet.h"
#include <gmpxx.h>


template<unsigned int D,class T>
class MonotoneConvexHull:public ConvexHull<D,T>{

	PointSet<D,T> & pointSet;
	ConvexPolygon<D,T> hull;

public:
	MonotoneConvexHull(PointSet<D,T> & p):pointSet(p){

	}

	void update();


	ConvexPolygon<D,T> & getHull(){
		update();
		return hull;
	}

private:
	T cross(const Point<D,T> &O, const Point<D,T> &A, const Point<D,T> &B);
};

// 2D cross product of OA and OB vectors, i.e. z-component of their 3D cross product.
// Returns a positive value, if OAB makes a counter-clockwise turn,
// negative for clockwise turn, and zero if the points are collinear.
//from http://en.wikibooks.org/wiki/Algorithm_Implementation/Geometry/Convex_hull/Monotone_chain
template<>
inline double MonotoneConvexHull<2,double>::cross(const Point2D &O, const Point2D &A, const Point2D &B)
{
	return (A[0] - O[0]) * (B[1] - O[1]) - (A[1] - O[1]) * (B[0] - O[0]);
}
template<>
void MonotoneConvexHull<1,double>::update();
template<>
void MonotoneConvexHull<2,double>::update();
template<>
void MonotoneConvexHull<3,double>::update();


template<>
inline mpq_class MonotoneConvexHull<2,mpq_class>::cross(const Point<2,mpq_class> &O, const Point<2,mpq_class> &A, const Point<2,mpq_class> &B)
{
	return (A[0] - O[0]) * (B[1] - O[1]) - (A[1] - O[1]) * (B[0] - O[0]);
}

template<>
void MonotoneConvexHull<2,mpq_class>::update();

#endif