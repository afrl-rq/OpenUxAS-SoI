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
#include <algorithm>

namespace uxas {
namespace service {
namespace monitoring {

typedef std::pair<double, double> coord_t;
typedef std::tuple<double, double, double> line_eq_t;

class MonitorPolygon;

struct IntervalList {
      IntervalList();
      IntervalList(IntervalList const & iList);
      void consolidate();
      bool invariant_check();
      void addInterval(double a, double b);
      bool coversUnit() const ;
      void printAll() const;

      std::vector< std::pair< double, double > > intervals;


};

class LineSegment {

public:
      LineSegment(int id, double xa, double ya, double xb, double yb, int numTestPoints=25);
      void registerSensorFootprint(MonitorPolygon const & mp);
      bool isSegmentCovered() const;
      int getID() const { return s_id; };
      void setDebug(bool d) { debug  = d; };
      void printIntervals() const { s_covered.printAll(); };
      double getRobustness() const { return *std::min_element(_robustness.begin(), _robustness.end()); };
protected:
      int s_id;
      coord_t s_A;
      coord_t s_B;
      line_eq_t s_C;
      IntervalList s_covered;
      bool debug;
      std::vector<coord_t> testPoints;
      std::vector<double> _robustness;
      void makeTestPoints(int k);
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
      std::tuple<bool, double> isMember(double x, double y) const;

protected:
      void computeHRepr();
      void addHalfSpace(coord_t const & ptA, coord_t const & ptB, coord_t const & testPt);

};




};
};
};



#endif
