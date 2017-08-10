/*
 * Author: Guohui
 * If you want to test it directly, using command in the terminal:
 * User$ g++ -o a.out VoronoiTest.cpp ../VoronoiDiagramGenerator.cpp ../GeometryUtilities.cpp -std=c++14
 */
#include <stdio.h>
#include <search.h>
#include <stdlib.h>
//#include <malloc.h>
#include "../VoronoiDiagramGenerator.h"
#include "../GeometryUtilities.h"
#include <iostream>
#include <string>

using namespace uxas::service::monitoring;

int main(int argc, char **argv) {
  //double xValues[] = {-22, -17, 4,22, 23};
  //double yValues[] = {-9, 31,13,-5, -7};
  //double xValues[] = {95.9492426392903,65.5740699156587,3.57116785741896,84.9129305868777,93.3993247757551,67.8735154857774,75.7740130578333,74.3132468124916,39.2227019534168,65.5477890177557,17.1186687811562,70.6046088019609};
  //double yValues[] = {3.18328463774207,27.6922984960890,4.61713906311539,9.71317812358475,82.3457828327293,69.4828622975817,31.7099480060861,95.0222048838355,3.44460805029088,43.8744359656398,38.1558457093008,76.5516788149002};
  // double xValues[] = {-31.4724,-40.5792,37.3013,-41.3376,-13.2359,40.246,22.1502,-4.6882,-45.7507,-46.4889,34.2387,-47.0593,-45.7167,1.4624,-30.028,35.8114,7.8239,-41.5736,-29.2207,-45.9492};
  //double yValues[] = {-15.5741,46.4288,-34.9129,-43.3993,-17.8735,-25.774,-24.3132,10.7773,-15.5478,32.8813,-20.6046,46.8167,22.3077,45.3829,40.2868,-32.3458,-19.4829,18.2901,-45.0222,46.5554};
  double xValues[] = {-55.9141,-67.753,33.4917,-68.7389,-32.2067,37.3197,13.7952,-21.0946,-74.4759,-75.4355,29.5103,-76.1771,-74.4317,-13.0988,-54.0365,31.5548,-4.829,-69.0456,-52.987,-74.734,-35.2463,45.3575,-60.3868,-71.4191,-38.2356,-48.5062,-46.6072,-0.98951,-35.2121,27.7457};
  double yValues[] = {0.57677,47.7717,30.6154,46.768,43.2008,-7.642,1.362,27.803,-16.5155,47.5888,19.2879,23.2909,-3.5862,-5.664,36.9189,15.7165,18.809,4.7581,0.34446,-2.8281,30.6782,2.4208,4.1431,38.6172,41.6702,15.1145,-17.1821,26.173,9.0313,34.3332};
  std::vector<std::pair<double, double> > input;
  for(int i = 0; i < sizeof(xValues)/sizeof(xValues[0]); i++) {
    std::pair<double, double> add;
    add.first = xValues[i];
    add.second = yValues[i];
    input.push_back(add);
  }
  std::cout <<  sizeof(xValues)/sizeof(xValues[0]) << std::endl;
  VoronoiDiagramGenerator vdg;
  //vdg.generateVDrectangle(input, -80, 60, -20, 60, 1);

  double radius = 40;
  std::pair<double, double> center = {-30, 22};
  vdg.generateVDcircle(input, center, radius);

  std::vector<std::pair<double, double> > polyBoundary;
  double boundx[] = {-73.6355,-53.0594,17.1241,21.8577,39.2063,37.6059,-64.6243,-83.8937};
  double boundy[] = {-50.7615,-59.4589,-35.6144,-31.1998,14.2853,78.3337,68.265,61.8131};
  for(int i = 0; i < sizeof(boundx)/sizeof(boundx[0]); i++) {
    std::pair<double, double> add;
    add.first = boundx[i];
    add.second = boundy[i];
    polyBoundary.push_back(add);
  }
  //vdg.generateVDpolygon(input, polyBoundary);
  
  vdg.hashTableOfSiteVDvertices();
  std::vector<std::pair<double, double> > conveshull = vdg.convexHullExpand(vdg.convexHullset(input), 20);

  std::cout << "-------------------------------" << std::endl;
  //for(auto item: vdg.VDedgeSet) std::cout << item.first.x << " " << item.first.y << " " << item.second.x << " " << item.second.y << std::endl;
  for(auto item: vdg.sites) {
    std::cout << "* " << vdg.VDvertices[item.sitemarker].size() << " ** "<< item.sitemarker << " : " << item.coord.x << " " << item.coord.y << std::endl;
    for(auto each: vdg.VDvertices[item.sitemarker]){
      std::cout << each.x << " " << each.y << std::endl;
    }
  }
  std::cout << "---------------Expanded Convex Hull----------------" << std::endl;
  for(auto item: conveshull) {
    std::cout << item.first << " " << item.second << std::endl;
  }
  std::cout << "--------------VD edges-----------------" << std::endl;
  for(auto item: vdg.VDedgeSet) {
    std::cout << item.first.x << " " << item.first.y << " " << item.second.x << " " << item.second.y << std::endl;
  }

  
  /*
  vdg.resetIterator();
  double x1,y1,x2,y2;
  
  std::cout << "-------------------------------" << std::endl;
  while(vdg.getNext(x1,y1,x2,y2))
  {
    //printf("GOT Line (%f,%f)->(%f,%f)\n",x1,y1,x2, y2);
    std::cout << x1 << " " << y1 << " " << x2 << " " << y2 << std::endl;
  }
  
  */
  return 0;
	
}



