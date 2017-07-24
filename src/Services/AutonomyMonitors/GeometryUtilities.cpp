#include <iostream>
#include <tuple>
#include <algorithm>
#include <limits>
#include <cassert>
#include "GeometryUtilities.h"

namespace uxas {
  namespace service {
    namespace monitoring {

      #define EPS 1E-06

      bool approx_equals(double a, double b){
	return (a >= b - EPS && a <= b + EPS); 
      }
      
      void computeSegmentEqFromEndPoints( coord_t const & ptA, coord_t const & ptB, line_eq_t & xc){
	double a, b, c;
	if (approx_equals(ptA.first, ptB.first)){
	  // Return the line 1.0 * x  + 0.0 * y - xa.first
	  a = 1.0;
	  b = 0.0;
	  c = -ptA.first;
	} else {
	  double m = (ptA.second - ptB.second)/(ptA.first - ptB.first); // Calculate the slope
	  // return the eq  y - m x + (m * xA - yA) = 0
	  b = 1.0;
	  a = - m;
	  c = m * ptA.first - ptA.second;
	}

	xc = std::make_tuple(a,b,c);
      }
      
      LineSegment::LineSegment(int id, double xa, double ya, double xb, double yb): s_id(id),
										    s_A(xa, ya),
										    s_B(xb, yb),
										    s_C(0.0, 0.0, 0.0)
      {
	computeSegmentEqFromEndPoints(s_A, s_B, s_C);
      }

      MonitorPolygon::MonitorPolygon(std::vector< coord_t > const & coOrdinates):p_coords(coOrdinates) {
	assert ( p_coords.size() >= 3);
	computeHRepr();
      }

      void MonitorPolygon::addHalfSpace(coord_t const & ptA, coord_t const & ptB, coord_t const & testPt){
	line_eq_t xc ;
	double a, b, c;
	computeSegmentEqFromEndPoints(ptA, ptB, xc);
	std::tie(a,b,c) = xc;
	computeSegmentEqFromEndPoints(ptA, ptB, xc);
	double val = a * testPt.first + b * testPt.second + c;
	if (approx_equals(val, 0.0)){
	  std::cerr << "FATAL: encountered polyhedron with collinear points." << std::endl;
	  assert(false);
	}
	
	if ( val < 0.0){
	  xc = std::make_tuple(-a, -b, -c);
	}
	if (debug){
	  std::cout<< "Halfspace: " << std::get<0>(xc) << "* x + " << std::get<1>(xc) << " *y + " << std::get<2>(xc) << " >= 0" << std::endl;
	}
	p_halfspaces.push_back(xc);
	return;
      }
      
      void MonitorPolygon::computeHRepr(){
	int n = p_coords.size();
	for (int i =0; i < n-1; ++i){
	  auto & ptA = p_coords[i];
	  auto & ptB = p_coords[i+1];
	  coord_t testPt;
	  if (i > 0){
	    testPt = p_coords[0];
	  } else {
	    testPt = p_coords[n-1];
	  }
	  addHalfSpace(ptA, ptB, testPt);
	}
	auto & ptX = p_coords[0];
	auto & ptY = p_coords[n-1];
	auto & ptTest = p_coords[1];
	addHalfSpace(ptY, ptX, ptTest);
      }

      void LineSegment::registerSensorFootprint(MonitorPolygon const & mp){
	/*--
	  1. Iterate through all the half-spaces of this polygon.
               1.1. Compute intersection with the segment
          2. Add interval
	  --*/
	static_assert(std::numeric_limits<double>::is_iec559, "IEEE 754 required");
	double lb = 0.0, ub = 1.0;
	double a,b,c;
	double lam;
	for (auto tup: mp.p_halfspaces){
	  a = b = c = 0.0;
	  std::tie(a,b,c) = tup;
	  double cA = s_A.first * a + s_A.second *b + c;
	  double cB = s_B.first * a + s_B.second *b + c;
	  
	  if (cA < -EPS  && cB > EPS){
	    // A is outside and B is inside
	    // This will affect the lower bound
	    lam = cA / (cA - cB);
	    assert (0 <= lam && lam <= 1.0);
	    lb = std::max(lb, lam);
	  }

	  if (cA > EPS && cB < -EPS){
	    lam = cA / (cA - cB);
	    assert( 0 <= lam && lam <= 1.0);
	    ub = std::min(ub, lam);
	  }

	  if (cA < EPS && cB < EPS){
	    // Both points are not robustly inside the halfspace
	    // This means that the sensor footprint is completely
	    // outside the line segment
	    return;
	  }
	}

	if (lb <= ub){
	  assert(0.0 <= lb && lb <= 1.0);
	  assert(0.0 <= ub && ub <= 1.0);
	  // if (debug)
	  // std::cout << "[GeometryUtilities:] Segment # " << this -> s_id << " covered interval: " << lb << " , " << ub << std::endl;
	  s_covered.addInterval(lb, ub);
	}

      }

      bool LineSegment::isSegmentCovered(){
	return s_covered.coversUnit();
      }


      IntervalList::IntervalList(){};
      IntervalList::IntervalList(IntervalList const & iList){
	for (auto p: iList.intervals){
	  intervals.push_back(p);
	}
      }
      
      bool IntervalList::invariant_check(){
	double lb = 0.0;
	/* make sure that the intervals are sorted according to their
	   lower bounds in ascending order. */
	for (auto & p: intervals){
	  if (p.first > p.second || p.first < 0.0 || p.second > 1.0)
	    return false;
	  if (p.first < lb)
	    return false;
	  lb = p.first;
	}
	return true;
      }
      
      void IntervalList::consolidate(){
	assert(invariant_check());
	auto it = intervals.begin();
	auto jt = it +1;
	while (it < intervals.end() && jt < intervals.end()){
	  auto & p = *it;
	  auto & q = *jt;
	  assert(p.first <= q.first);
	  if (p.second < q.first) {
	    it ++;
	    continue;
	  } else {
	    // They can be merged.
	    p.second = std::max(q.second, p.second);
	    jt = intervals.erase(jt);
	  }
	}
      }
      
      void IntervalList::addInterval(double a, double b){
	a = std::max(a, 0.0);
	b = std::min(b, 1.0);
	if (a < b){
	  // First find out where a fits
	  std::pair<double, double> pr (a, b);
	  if (intervals.size() == 0){
	    intervals.push_back( pr);
	  } else {
	    auto it = intervals.begin();
	    while (it < intervals.end() && it -> first < a)
	      ++it;
	    intervals.insert(it, pr);
	    consolidate();
	  }

	  return;
	}
      }

      bool IntervalList::coversUnit(){
	if (intervals.size() != 1){
	  return false;
	}
	auto p = *(intervals.begin());
	return (p.first <= EPS && p.second >= 1.0 - EPS);
      }

      void IntervalList::printAll(){
	std::cout << "Interval List: " << std::endl;
	for (auto iv: intervals){
	  std::cout << "\t Covered: " << iv.first << " , " << iv.second << std::endl;
	}
      }
      
    };
  };
};
