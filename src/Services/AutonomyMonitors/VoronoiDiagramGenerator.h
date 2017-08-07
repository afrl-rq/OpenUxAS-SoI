/*
 * The author of this software is Steven Fortune.  Copyright (c) 1994 by AT&T
 * Bell Laboratories.
 * Permission to use, copy, modify, and distribute this software for any
 * purpose without fee is hereby granted, provided that this entire notice
 * is included in all copies of any software which is or includes a copy
 * or modification of this software and in all copies of the supporting
 * documentation for such software.
 * THIS SOFTWARE IS BEING PROVIDED "AS IS", WITHOUT ANY EXPRESS OR IMPLIED
 * WARRANTY.  IN PARTICULAR, NEITHER THE AUTHORS NOR AT&T MAKE ANY
 * REPRESENTATION OR WARRANTY OF ANY KIND CONCERNING THE MERCHANTABILITY
 * OF THIS SOFTWARE OR ITS FITNESS FOR ANY PARTICULAR PURPOSE.
 */

/*
 * Author Guohui and Sriram
 */

#ifndef VORONOI_DIAGRAM_GENERATOR
#define VORONOI_DIAGRAM_GENERATOR

#include <math.h>
#include <stdlib.h>
#include <string.h>
#include <iostream>
#include <vector>
#include <queue>
#include <unordered_map>
#include <stack>
#include <algorithm>


#define DELETED -2
#define EPS 1.0e-8

#define LEFTedge 0
#define RIGHTedge 1

// They are used for sites and VD vertices
struct Point {
  double x, y;
};

// Structure used both for sites and for vertices 
struct Site {
  struct Point coord;
  int sitemarker; // Index of each site based on the initial input sites
  int visited; // Reference of site to show whether it is used or not
};

struct Edge {
  double a, b, c; // Line expression of the bisector: ax + by = c
  struct Site *bisectSeg[2]; // The bisector's start/end points
  struct Site *siteSeg[2]; // The start/end points of the site
  int edgenbr;
};

struct GraphEdge {
  double x1, y1, x2, y2;
  struct GraphEdge* next;
};

struct VoronoiEdge { //
  struct VoronoiEdge *leftVedge, *rightVedge; // vertex's neightbors
  struct Edge *innerVedge;
  //int ELrefcnt;
  char ELpm;
  struct Site *vertex; //
  double ystar; // Lowest y-coordinate of the hyperbola
  struct VoronoiEdge *PQnext; //
};

class VoronoiDiagramGenerator {
public:
  std::unordered_map<int, std::vector<struct Point> > VDvertices;
  std::vector<std::pair<int, int> > VDedgeSetHelper;
  
  std::vector<std::pair<struct Point, struct Point> >VDedgeSet;
  int VDverticesNumber; // Number of Voronoi diagram vertices
  int siteNumber; // Number of sites
  std::vector<struct Site> sites;
  
  VoronoiDiagramGenerator();
  ~VoronoiDiagramGenerator();
  bool generateVDrectangle(std::vector<std::pair<double, double> > viewAngleList, double lowerBorderX, double upperBorderX, double lowerBorderY, double upperBorderY, double minDist=0);
  bool generateVDcircle(std::vector<std::pair<double, double> > viewAngleList, std::pair<double, double> Center, double Radius, double minDist=0);
  bool generateVDpolygon(std::vector<std::pair<double, double> > viewAngleList, std::vector<std::pair<double, double> > polyBoundary, double minDist=0);
  void hashTableOfSiteVDvertices();

  std::vector<std::pair<double, double> > convexHullset(std::vector<std::pair<double, double> > viewAngleList);
  std::vector<std::pair<double, double> > convexHullExpand(std::vector<std::pair<double, double> > chBoundary, double moat);

  
  void resetIterator() {
    iteratorEdges = allEdges;
  }

  bool getNext(double& x1, double& y1, double& x2, double& y2) {
    if(iteratorEdges == 0) return false;
    x1 = iteratorEdges->x1;
    x2 = iteratorEdges->x2;
    y1 = iteratorEdges->y1;
    y2 = iteratorEdges->y2;
    iteratorEdges = iteratorEdges->next;

    return true;
  }

private:
  /* Fundamental components */
  int searchAreaType; // 0: circle, 1: rectangle, 2: polygon
  GraphEdge* allEdges;
  GraphEdge* iteratorEdges;
  struct sort_pred {
    bool operator() (const Site &a, const Site &b) {
      return a.coord.y < b.coord.y || (a.coord.y == b.coord.y && a.coord.x < b.coord.x);
    }
  };
  
  int edgeNumber; // Number of edges
  
  int siteIndex; // Index of current site
  double gapThreshold;
  struct Site *bottomsite;
  
  
  /* Main operation */
  bool voronoiOperation();

  
  /* Priority queue for the sites and intersections on the plane */
  int PQsize;
  VoronoiEdge *PQtable; // Priority queue of sites and intersections
  bool PQinit();
  int PQempty();
  struct Point PQtop();
  struct VoronoiEdge *PQpopMin();
  void PQinsert(struct VoronoiEdge *current, struct Site *v, double offset);
  void PQdelete(struct VoronoiEdge *VDedge);
  
  
  /* EdgeList */
  struct VoronoiEdge *EdgeListLeftBorder, *EdgeListRightBorder; // ELhash's range
  //int ELhashsize;
  bool EdgeListInit();
  void EdgeListInsert(struct VoronoiEdge *current, struct VoronoiEdge *newVDedge);
  void EdgeListDelete(struct VoronoiEdge *VDedge);
  struct VoronoiEdge *leftVoronoiEdge(struct Point *node);

  
  /* Geometry operations */
  struct Edge *generateBisector(struct Site *s1, struct Site *s2);
  double distance(struct Site *s1, struct Site *s2);
  double distPoint(struct Point s1, struct Point s2);
  double distpair(std::pair<double, double> s1, std::pair<double, double> s2);
  double distPointToLineABC(std::pair<double, double> innerPoint, double a, double b, double c);
  
  
  struct Site *generateIntersection(struct VoronoiEdge *VDedge1, struct VoronoiEdge *VDedge2);
  bool segIntersectSeg(std::pair<struct Point, struct Point> &edge, std::pair<struct Point, struct Point> boundary, struct Point &intersect);
  int rightCheck(struct VoronoiEdge *VDedge, struct Point *node);
  struct Site *rightSite(struct VoronoiEdge *VDedge);
  struct Site *leftSite(struct VoronoiEdge *VDedge);
  int orientation(std::pair<double, double> p0, std::pair<double, double> a, std::pair<double, double> b);
  
  


  /* Additional operations */
  double xmin, xmax, ymin, ymax;
  double borderMinX, borderMaxX, borderMinY, borderMaxY;
  //void geominit();
  void usedMark(struct Site *st);
  void unusedMark(struct Site *st);
  
  void endPoint(struct Edge *edge, int pos,struct Site *st);
  void generateVDvertex(struct Site *st);
  struct Site *nextone();
  void VDedgeGenerator(struct Edge *VDedge);
  void pushGraphEdge(double x1, double y1, double x2, double y2);

  struct VoronoiEdge *HEcreate(struct Edge *edge, int pm);
  
};


#endif


