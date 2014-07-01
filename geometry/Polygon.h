/*
 * Polygon.h
 *
 *  Created on: 2014-02-23
 *      Author: sam
 */

#ifndef POLYGON_H_
#define POLYGON_H_
#include <math.h>
#include "Shape.h"
#include <gmpxx.h>
/**
 * A concrete polygon (or, for D>2, a polytope)
 */
template<unsigned int D,class T>
class Polygon:public Shape<D,T>{
public:
	//List of vertices in clockwise order
	std::vector<Point<D,T>> vertices;
	Point<D,T> circleCenter;//should generalize this to an arbitrary bounding volume...
	T circleRadius;
	bool vertices_clockwise=false;
	virtual ~Polygon(){};
	virtual ShapeType getType(){
		return POLYGON;
	}
	virtual bool contains(const Point<D,T> & point);

	virtual bool intersects(Shape<D,T> & s){
		return false;
	}

	int size()const {
		return vertices.size();
	}

	void update(){
		if(!vertices_clockwise){
			reorderVertices();
		}
		updateCircleBound();
	}

	void clear(){
		vertices.clear();
	}

	int size(){
		return vertices.size();
	}

	void addVertex(Point<D,T> & p){
		vertices_clockwise=false;
		vertices.push_back(p);
	}
	//add a vertex, assuming that it will preserve clockwise order
	void addVertexUnchecked(Point<D,T> & p){
		vertices.push_back(p);
		assert(dbg_orderClockwise());
	}

	void popVertex(){
		vertices.pop();
	}

	void clearVertices(){
		vertices.clear();
	}

	//Returns the vertices of the polygon, in clockwise order.

	std::vector<Point<D,T> > & getVertices(){
		if(!vertices_clockwise){
			reorderVertices();
		}
		dbg_orderClockwise();
		return vertices;
	}
    const Point<D,T>& operator [] (int index) const {
    	index = index %vertices.size();
    	if(index<0){
    		index+=vertices.size();
    	}
    	assert(index>=0);assert(index<vertices.size());
    	return vertices[index];
    }
    Point<D,T>&       operator [] (int index)       {
    	index = index %vertices.size();
    	if(index<0){
    		index+=vertices.size();
    	}
    	assert(index>=0);assert(index<vertices.size());
    	return vertices[index];
    }

	void updateCircleBound();
	virtual T getArea();
	virtual T getPerimeter();
	//put the vertices into clockwise order
	void reorderVertices();
protected:
	bool dbg_orderClockwise(){
		return true;
	}
private:




	//Note: for convenience, the first point of the wrap is also the last point (it is duplicated).
	template< class ValueType >
	struct wrap_iterator {
	    ValueType &operator*() { return verts[pos%verts.size()]; }



	    wrap_iterator operator++() { wrap_iterator i = *this; pos++; return i; }
	    wrap_iterator operator++(int ignore) { pos++; return *this; }
	    ValueType* operator->() { return &verts[pos%verts.size()]; }
	    bool operator==(const wrap_iterator& rhs) { return pos == rhs.pos; }
	    bool operator!=(const wrap_iterator& rhs) { return pos != rhs.pos; }

	    int pos=0;
	    std::vector<ValueType> & verts;


	    wrap_iterator( std::vector<ValueType> & verts, int pos):verts(verts),pos(pos){}; // private constructor for begin, end
	};

	typedef wrap_iterator<  Point<D,T> > iterator;
	typedef wrap_iterator<  Point<D,T> const > const_iterator;
public:
	 iterator begin()
	{
		 return iterator(getVertices(),0);
	}

	iterator end()
	{
		return iterator(getVertices(),getVertices().size());
	}

	iterator end_wrap()
	{
		return iterator(getVertices(),getVertices().size()+1);
	}

/*	 const_iterator begin() const
	{
		 return const_iterator(vertices,0);
	}

	const_iterator end() const
	{
		return const_iterator(vertices,vertices.size());
	}

	const_iterator end_wrap() const
	{
		return const_iterator(vertices,vertices.size()+1);
	}*/
};

template<>
inline bool Polygon<2,double>::dbg_orderClockwise(){
#ifndef NDEBUG
	//from http://stackoverflow.com/a/1165943
	if(vertices_clockwise){
		double sum = 0;
		for(int i = 0;i<vertices.size();i++){
			Point<2,double> & a = i>0? vertices[i-1]:vertices.back();
			Point<2,double> & b = vertices[i];
			sum+= (b.x - a.x)*(b.y+a.y);
		}
		assert(sum>=0);
	}

#endif
	return true;
}
template<>
bool Polygon<2,double>::contains(const Point<2,double> & point);

template<>
void Polygon<2,double>::reorderVertices();

template<>
double Polygon<2,double>::getArea();

template<>
double Polygon<2,double>::getPerimeter();



template<>
inline bool Polygon<2,mpq_class>::dbg_orderClockwise(){
#ifndef NDEBUG
	//from http://stackoverflow.com/a/1165943
	if(vertices_clockwise){
		mpq_class sum = 0;
		for(int i = 0;i<vertices.size();i++){
			Point<2,mpq_class> & a = i>0? vertices[i-1]:vertices.back();
			Point<2,mpq_class> & b = vertices[i];
			sum+= (b.x - a.x)*(b.y+a.y);
		}
		assert(sum>=0);
	}

#endif
	return true;
}
template<>
bool Polygon<2,mpq_class>::contains(const Point<2,mpq_class> & point);

template<>
void Polygon<2,mpq_class>::reorderVertices();

template<>
mpq_class Polygon<2,mpq_class>::getArea();

template<>
mpq_class Polygon<2,mpq_class>::getPerimeter();


template<unsigned int D,class T>
void Polygon<D,T>::updateCircleBound(){
	circleCenter.zero();
	for(int i = 0;i<vertices.size();i++){
		circleCenter+=vertices[i];
	}
	circleCenter/=T(vertices.size());
	circleRadius=T(0);
	for(int i = 0;i<vertices.size();i++){
		T dist = circleCenter.distance( vertices[i]);
		if(dist>circleRadius){
			circleRadius=dist;
		}
	}
}

#endif /* POLYGON_H_ */