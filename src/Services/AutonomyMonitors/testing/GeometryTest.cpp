#include "GeometryUtilities.h"

using namespace uxas::service::monitoring;

void test1(){
  // Create a polygon and a line segment
  LineSegment ls1(1, -3.0,2.0, 3.0, -2.0);
  ls1.setDebug(true);
  std::vector<coord_t> poly_coords1 {coord_t(-1.0, 2.0), coord_t(-1.0, -2.0), coord_t(1.0, -1.0), coord_t(1.0, 0.5)};
  MonitorPolygon mp1(poly_coords1);
  ls1.registerSensorFootprint(mp1);
  std::vector<coord_t> poly_coords2 {coord_t(-0.8,1.9), coord_t(-0.79, -1.9), coord_t(1.25, -0.9), coord_t(1.2, 0.6)};
  MonitorPolygon mp2(poly_coords2);
  ls1.registerSensorFootprint(mp2);
  ls1.printIntervals();
  return;
}

void test2(){
  IntervalList iList;

  iList.addInterval(0, 0.24);
  iList.addInterval(0, 0.5);
  iList.addInterval(0, 1);
  iList.addInterval(0, 1);
  
  iList.printAll();
  if (iList.coversUnit()){
    std::cout << "YEAH!" << std::endl;
  }
}

int main(){
  test1();
  test2();
}
