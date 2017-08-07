
/*
 * Author: Guohui and Sriram
 */
#include <stdio.h>
#include <search.h>
#include <stdlib.h>
//#include <malloc.h>
#include "VoronoiDiagramGenerator.h"
#include <iostream>
#include <string>


int main(int argc,char **argv) {

  double xValues[] = {-22, -17, 4,22, 23};
  double yValues[] = {-9, 31,13,-5, -7};
  //double xValues[] = {95.9492426392903,65.5740699156587,3.57116785741896,84.9129305868777,93.3993247757551,67.8735154857774,75.7740130578333,74.3132468124916,39.2227019534168,65.5477890177557,17.1186687811562,70.6046088019609};
  //double yValues[] = {3.18328463774207,27.6922984960890,4.61713906311539,9.71317812358475,82.3457828327293,69.4828622975817,31.7099480060861,95.0222048838355,3.44460805029088,43.8744359656398,38.1558457093008,76.5516788149002};
  std::vector<std::pair<double, double> > input;
  for(int i = 0; i < 5; i++) {
    std::pair<double, double> add;
    add.first = xValues[i];
    add.second = yValues[i];
    input.push_back(add);
  }

  VoronoiDiagramGenerator vdg;
  //vdg.generateVDrectangle(input, -100, 100, -100, 100, 1);

  double radius = 80;
  std::pair<double, double> center = {0, 0};
  //vdg.generateVDcircle(input, center, radius);

  std::vector<std::pair<double, double> > polyBoundary;
  double boundx[] = {-30, 60, 100, 100, 30, -60, -100, -100};
  double boundy[] = {100, 100, 70, -20, -100, -100, -80, 10};
  for(int i = 0; i < 8; i++) {
    std::pair<double, double> add;
    add.first = boundx[i];
    add.second = boundy[i];
    polyBoundary.push_back(add);
  }
  polyBoundary.push_back(polyBoundary.front());
  vdg.generateVDpolygon(input, polyBoundary);
  
  
  vdg.hashTableOfSiteVDvertices();
  vdg.resetIterator();
  double x1,y1,x2,y2;
  
  std::cout << "-------------------------------" << std::endl;
  while(vdg.getNext(x1,y1,x2,y2))
  {
    //printf("GOT Line (%f,%f)->(%f,%f)\n",x1,y1,x2, y2);
    //std::cout << x1 << " " << y1 << " " << x2 << " " << y2 << std::endl;
  }
  for(auto item: vdg.VDedgeSet) {
    std::cout << item.first.x << " " << item.first.y << " " << item.second.x << " " << item.second.y << std::endl;
  }
  std::cout << "-------------------------------" << std::endl;
  //for(auto item: vdg.VDedgeSet) std::cout << item.first.x << " " << item.first.y << " " << item.second.x << " " << item.second.y << std::endl;
  for(auto item: vdg.sites) {
    std::cout << "** " << vdg.VDvertices[item.sitemarker].size() << " **"<< item.sitemarker << ": " << item.coord.x << " " << item.coord.y << std::endl;
    for(auto each: vdg.VDvertices[item.sitemarker]){
      std::cout << each.x << " " << each.y << std::endl;
    }
    
  }
  
  return 0;
	
}



