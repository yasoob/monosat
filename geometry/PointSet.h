
#ifndef POINTSET_H_
#define POINTSET_H_
#include <vector>
#include "GeometryTypes.h"
/**
 * A dynamic point set
 */
template<unsigned int D,class T=double>
class PointSet{
	//Dimension of this shape
	std::vector<Point<D,T>> points;
	bool hasClockwise = false;
	std::vector<int> points_clockwise;
	std::vector<bool> enabled;
	int sz;
	int num_enabled= 0;

	void buildClockwise();

public:

	int dimension(){
		return D;
	}
	int size()const{
		return sz;
	}
	int fullSize()const{
		return points.size();
	}
	int nEnabled() const{
		return num_enabled;
	}
	bool isEnabled(int pointID){
		return enabled[pointID];
	}
	bool pointEnabled(int pointID){
		return  enabled[pointID];
	}
	void disablePoint(int pointID){
		setPointEnabled(pointID, false);
	}
	void enablePoint(int pointID){
		setPointEnabled(pointID, true);
	}

	//returns indices of all points (including disabled points!) in clockwise order
	std::vector<int> & getClockwisePoints(){
		if(!hasClockwise){
			buildClockwise();
		}
		return points_clockwise;
	}

	void setPointEnabled(int pointID, bool _enabled){
		if(isEnabled(pointID)==_enabled)
			return;
		enabled[pointID]=_enabled;
		if(_enabled){
			num_enabled++;
		}else{
			num_enabled--;
		}
	}

	std::vector<Point<D,T>> & getEnabledPoints(std::vector<Point<D,T>> & points_out){
		points_out.clear();
		for(int i = 0;i<points.size();i++){
			if(isEnabled(i)){
				points_out.push_back(points[i]);
			}
		}
		return points_out;
	}

	int addPoint(const Point<D,T> & P, int pointID=-1){
		if(pointID<0)
			pointID=points.size();
		points.push_back(P);
		points.back().setID(pointID);
		enabled.push_back(false);
		hasClockwise=false;
		sz++;
		return pointID;
	}

    const Point<D,T>& operator [] (int index) const { return points[index]; }
    Point<D,T>&       operator [] (int index)       { return points[index]; }
	void clearHistory(){

	}
	void clearChanged(){

	}
	void markChanged(){

	}
	void invalidate(){

	}
};

template<>
void PointSet<2,double>::buildClockwise();

#endif /* SHAPE_H_ */