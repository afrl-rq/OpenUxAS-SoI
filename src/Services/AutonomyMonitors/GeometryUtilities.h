#ifndef D__GEOMETRY__UTILITIES__H__
#define D__GEOMETRY__UTILITIES__H__

/**
 * GeometryUtilities: 
 * Functions for managing lines, polygons, intersections and the various geometry processing tasks 
 * for the autonomy monitor.
 *
 */

#include <vector>
#include <iostream>
#include <tuple>

namespace uxas{
  namespace service {
    namespace monitoring {

      typedef std::pair<double, double> coord_t;
      typedef std::tuple<double, double, double> line_eq_t;

      class MonitorPolygon;

      struct IntervalList{
	IntervalList();
	IntervalList(IntervalList const & iList);
	void consolidate();
	bool invariant_check();
	void addInterval(double a, double b);
	bool coversUnit();
	void printAll();
	
	std::vector< std::pair< double, double > > intervals;

	
      };
      
      class LineSegment {
	
      public:
	LineSegment(int id, double xa, double ya, double xb, double yb);
	void registerSensorFootprint(MonitorPolygon const & mp);
	bool isSegmentCovered();
	int getID() const { return s_id; };
	void setDebug(bool d){ debug  =d; };
	void printIntervals(){ s_covered.printAll(); };
      protected:
	int s_id;
	coord_t s_A;
	coord_t s_B;
	line_eq_t s_C;
	IntervalList s_covered;
	bool debug;
      };

      class MonitorPolygon {
      protected:
	std::vector<coord_t> p_coords;
	std::vector<line_eq_t> p_halfspaces;
	bool debug;
      public:
	MonitorPolygon(std::vector< coord_t > const & coOrdinates);
	friend void LineSegment::registerSensorFootprint(MonitorPolygon const & mp);
	void setDebug(bool d) { debug = d;};
      protected:
	void computeHRepr();
	void addHalfSpace(coord_t const & ptA, coord_t const & ptB, coord_t const & testPt);
	
      };
      

      
      
    };
  };
};



#endif
