/*
 * The author of this software is Steven Fortune.  Copyright (c) 1994 by AT&T
 * Bell Laboratories.
 * Permission to use, copy, modify, and distribute this software for any
 * purpose with fee is hereby granted, provided that this entire notice
 * is included in all copies of any software which is or includes a copy
 * or modification of this software and in all copies of the supporting
 * documentation for such software.
 * THIS SOFTWARE IS BEING PROVIDED "AS IS", WITHOUT ANY EXPRESS OR IMPLIED
 * WARRANTY.  IN PARTICULAR, NEITHER THE AUTHORS NOR AT&T MAKE ANY
 * REPRESENTATION OR WARRANTY OF ANY KIND CONCERNING THE MERCHANTABILITY
 * OF THIS SOFTWARE OR ITS FITNESS FOR ANY PARTICULAR PURPOSE.
 */

/*
 * Author: Guohui and Sriram
 */

#include "VoronoiDiagramGenerator.h"
#include "GeometryUtilities.h"

namespace uxas {
namespace service {
namespace monitoring {
  
VoronoiDiagramGenerator::VoronoiDiagramGenerator() {
  siteIndex = 0;
  allEdges = 0;
  iteratorEdges = 0;
  gapThreshold = 0;
}

VoronoiDiagramGenerator::~VoronoiDiagramGenerator() {}

bool VoronoiDiagramGenerator::generateVDrectangle(std::vector<std::pair<double, double>> viewAngleList, double lowerBorderX, double upperBorderX, double lowerBorderY, double upperBorderY, double minDist) {
  if(viewAngleList.empty()) return false;
  if((upperBorderX - lowerBorderX < EPS && upperBorderX - lowerBorderX > -EPS) || (upperBorderY - lowerBorderY < EPS && upperBorderY - lowerBorderY > -EPS)) return false;
  
  gapThreshold = minDist;
  siteNumber = viewAngleList.size();

  xmin = viewAngleList[0].first;
  ymin = viewAngleList[0].second;
  xmax = viewAngleList[0].first;
  ymax = viewAngleList[0].second;
  
  sites.resize(siteNumber);
  for(int i = 0; i < siteNumber; i++) {
    sites[i].coord.x = viewAngleList[i].first;
    sites[i].coord.y = viewAngleList[i].second;
    sites[i].sitemarker = i;
    sites[i].visited = 0;

    if(viewAngleList[i].first < xmin) xmin = viewAngleList[i].first;
    else if(viewAngleList[i].first > xmax) xmax = viewAngleList[i].first;

    if(viewAngleList[i].second < ymin) ymin = viewAngleList[i].second;
    else if(viewAngleList[i].second > ymax) ymax = viewAngleList[i].second;
  }
  
  sort(sites.begin(), sites.end(), sort_pred());

  siteIndex = 0;
  VDverticesNumber = 0;
  edgeNumber = 0;

  if(lowerBorderX > upperBorderX) std::swap(lowerBorderX, upperBorderX);
  if(lowerBorderY > upperBorderY) std::swap(lowerBorderY, upperBorderY);
  
  borderMinX = lowerBorderX;
  borderMinY = lowerBorderY;
  borderMaxX = upperBorderX;
  borderMaxY = upperBorderY;
  
  siteIndex = 0;
  voronoiOperation();
 
  return true;
}

bool VoronoiDiagramGenerator::generateVDcircle(std::vector<std::pair<double, double> > viewAngleList, std::pair<double, double> Center, double Radius,  double minDist) {
  if(viewAngleList.empty()) return false;
  if(Radius < EPS && Radius > -EPS) return false;
  
  double upperBorderX = Center.first + Radius;
  double lowerBorderX = Center.first - Radius;
  double upperBorderY = Center.second + Radius;
  double lowerBorderY = Center.second - Radius;
  // Find the maximal area for the area
  generateVDrectangle(viewAngleList, lowerBorderX, upperBorderX, lowerBorderY, upperBorderY, minDist);
  
  struct Point stCenter;
  stCenter.x = Center.first;
  stCenter.y = Center.second;
  for(int i = 0; i < VDedgeSet.size(); i++) {
    struct Point *s1 = &VDedgeSet[i].first;
    struct Point *s2 = &VDedgeSet[i].second;
    if(s1 == (struct Point *) NULL || s2 == (struct Point *) NULL) continue;
    // Equations of cirlce and line, where unknown variable is the ratio between
    // end points of line segment
    double A = distPoint(*s1, *s2) * distPoint(*s1, *s2);
    double B = 2*((s2->x - s1->x)*(s1->x - Center.first) + (s2->y - s1->y)*(s1->y - Center.second));
    double C = Center.first * Center.first + Center.second * Center.second + s1->x * s1->x + s1->y * s1->y - 2*(Center.first * s1->x + Center.second * s1->y) - Radius*Radius;
    double delta = B*B - 4*A*C;
    struct Site *site1 = &VDedgeSetHelper[i].first;
    struct Site *site2 = &VDedgeSetHelper[i].second;
    if(distPoint(site1->coord, stCenter) <= Radius && distPoint(site2->coord, stCenter) > Radius) {
      *site2 = *site1;
    } else if(distPoint(site1->coord, stCenter) > Radius && distPoint(site2->coord, stCenter) <= Radius) {
      *site1 = *site2;
    } else if(distPoint(site1->coord, stCenter) > Radius && distPoint(site2->coord, stCenter) > Radius) {
      site2 = (struct Site *) NULL;
      site1 = (struct Site *) NULL;
    }
    
    
    if(distPoint(*s1, stCenter) <= Radius && distPoint(*s2, stCenter) <= Radius) {
      continue;
    } else if(distPoint(*s1, stCenter) > Radius && distPoint(*s2, stCenter) > Radius) {
      // Remove the edges outside of the area
      VDedgeSet.erase(VDedgeSet.begin() + i);
      VDedgeSetHelper.erase(VDedgeSetHelper.begin() + i);
      i--;
    } else {
      if(delta > EPS) {
        // Possible ratio
        double u1 = (-B + sqrt(delta))/(2*A);
        double u2 = (-B - sqrt(delta))/(2*A);

        if((u1 >= EPS && u1 <= 1) && (u2 < -EPS || u2 > 1)) {
          if(distPoint(*s1, stCenter) <= Radius) {
            s2->x = s1->x + u1*(s2->x - s1->x);
            s2->y = s1->y + u1*(s2->y - s1->y);
            
          }
          else{
            s1->x = s1->x + u1*(s2->x - s1->x);
            s1->y = s1->y + u1*(s2->y - s1->y);
          }
        } else if((u2 >= EPS && u2 <= 1) && (u1 < -EPS || u1 > 1)) {
          if(distPoint(*s1, stCenter) <= Radius) {
            s2->x = s1->x + u2*(s2->x - s1->x);
            s2->y = s1->y + u2*(s2->y - s1->y);
          }
          else{
            s1->x = s1->x + u2*(s2->x - s1->x);
            s1->y = s1->y + u2*(s2->y - s1->y);
          }
        } else if((u2 >= EPS && u2 <= 1) && (u1 >= EPS || u1 <= 1)) {
          s1->x = s1->x + u1*(s2->x - s1->x);
          s1->y = s1->y + u1*(s2->y - s1->y);
          s2->x = s1->x + u2*(s2->x - s1->x);
          s2->y = s1->y + u2*(s2->y - s1->y);
        }
      }
    }
  }
  
  return true;
}

double VoronoiDiagramGenerator::distPoint(struct Point s1, struct Point s2) {
  return sqrt(pow(s1.x - s2.x, 2) + pow(s1.y - s2.y, 2));
}
  
// Input polyBoundary should be clockwise or counterclockwise, and it doesn't
// have the same point.
bool VoronoiDiagramGenerator::generateVDpolygon(std::vector<std::pair<double, double> > viewAngleList, std::vector<std::pair<double, double> > polyBoundary, double minDist) {
  
  if(viewAngleList.empty()) return false;
  
  std::pair<double, double> Xpoint=polyBoundary[0], Ypoint=polyBoundary[0];
  // Find the external rectangle of polyboundary
  for(auto item: polyBoundary) {
    Xpoint.first = std::min(Xpoint.first, item.first); // X-min
    Xpoint.second = std::max(Xpoint.second, item.first); // X-max
    Ypoint.first = std::min(Ypoint.first, item.second); // Y-min
    Ypoint.second = std::max(Ypoint.second, item.second); // Y-max
  }
  
  generateVDrectangle(viewAngleList, Xpoint.first, Xpoint.second, Ypoint.first, Ypoint.second, minDist);

  MonitorPolygon boundaryArea(polyBoundary);
  double something;
  long length = polyBoundary.size();
  for(int i = 0; i < VDedgeSet.size(); i++) {
    bool isInArea1 = false, isInArea2 = false;
    std::tie(isInArea1, something) = boundaryArea.isMember(VDedgeSet[i].first.x, VDedgeSet[i].first.y);
    std::tie(isInArea2, something) = boundaryArea.isMember(VDedgeSet[i].second.x, VDedgeSet[i].second.y);
    if(isInArea1 && isInArea2) continue;
    else if(isInArea1 && !isInArea2) {
      for(int j = 0; j < length; j++) {
        struct Point intersect;
        std::pair<struct Point, struct Point> boundary;
        boundary.first.x = polyBoundary[j].first;
        boundary.first.y = polyBoundary[j].second;
        boundary.second.x = polyBoundary[(j+1) % length].first;
        boundary.second.y = polyBoundary[(j+1) % length].second;
        
        if(segIntersectSeg(VDedgeSet[i], boundary, intersect)) {
          VDedgeSet[i].second = intersect;
          //break;
        }
      }
    } else if(!isInArea1 && isInArea2) {
      for(int j = 0; j < length; j++) {
        struct Point intersect;
        std::pair<struct Point, struct Point> boundary;
        boundary.first.x = polyBoundary[j].first;
        boundary.first.y = polyBoundary[j].second;
        boundary.second.x = polyBoundary[(j+1) % length].first;
        boundary.second.y = polyBoundary[(j+1) % length].second;
        
        if(segIntersectSeg(VDedgeSet[i], boundary, intersect)) {
          VDedgeSet[i].first = intersect;
          //break;
        }
      }
    } else {
      VDedgeSet.erase(VDedgeSet.begin() + i);
      VDedgeSetHelper.erase(VDedgeSetHelper.begin() + i);
      i--;
    }
  }

  return true;
}

bool VoronoiDiagramGenerator::segIntersectSeg(std::pair<struct Point, struct Point> &edge, std::pair<struct Point, struct Point> boundary, struct Point &intersect) {
  // Check whether two line segments are intersected or not
  //if(edge.first.x > edge.second.x) std::swap(edge.first, edge.second);
  //if(boundary.first.x > boundary.second.x) std::swap(boundary.first, boundary.second);
  //if(std::max(edge.first.x, boundary.first.x) > std::min(edge.second.x, boundary.second.x)) return false;

  // Find the intersection
  double x1 = edge.first.x, x2 = edge.second.x;
  double y1 = edge.first.y, y2 = edge.second.y;
  double x3 = boundary.first.x, x4 = boundary.second.x;
  double y3 = boundary.first.y, y4 = boundary.second.y;
  double denominator = (y4 - y3)*(x2 - x1) - (x4 - x3) * (y2 - y1);
  if(denominator > -EPS && denominator < EPS) return false;

  double ua = (x4 - x3) * (y1 - y3) - (y4 - y3) * (x1 - x3);
  ua = ua / denominator;
  double ub = (x2 - x1) * (y1 - y3) - (y2 - y1) * (x1 - x3);
  ub = ub / denominator;

  if((ua <= 1 && ua >= EPS) && (ub <= 1 && ub >= EPS)) {
    intersect.x = x1 + ua * (x2 - x1);
    intersect.y = y1 + ua * (y2 - y1);
  } else return false;
  
  return true;
}

void VoronoiDiagramGenerator::hashTableOfSiteVDvertices() {
  for(int i = 0; i < VDedgeSetHelper.size(); i++) {
    if(&VDedgeSetHelper[i].first != (struct Site *) NULL) {
      VDvertices[VDedgeSetHelper[i].first.sitemarker].push_back(VDedgeSet[i].first);
      VDvertices[VDedgeSetHelper[i].first.sitemarker].push_back(VDedgeSet[i].second);
    }
    if(&VDedgeSetHelper[i].second != (struct Site *) NULL) {
      VDvertices[VDedgeSetHelper[i].second.sitemarker].push_back(VDedgeSet[i].first);
      VDvertices[VDedgeSetHelper[i].second.sitemarker].push_back(VDedgeSet[i].second);
    }
  }
  
  std::cout << sites.size() << std::endl;
  for(int i = 0; i < sites.size(); i++) {
    if(VDvertices[sites[i].sitemarker].empty()) continue;
    sort(VDvertices[sites[i].sitemarker].begin(), VDvertices[sites[i].sitemarker].end(), [](const Point &a, const Point &b) {
        return a.y < b.y || (a.y == b.y && a.x < b.x);
      });
    for(int j = 0; j < VDvertices[sites[i].sitemarker].size() - 1; j++) {
      double diff = VDvertices[sites[i].sitemarker][j].y - VDvertices[sites[i].sitemarker][j+1].y;
      if(diff > -EPS && diff < EPS) {
        VDvertices[sites[i].sitemarker].erase(VDvertices[sites[i].sitemarker].begin() + j+1);
        j--;
      }
    }
  }
  
}

/******************************************************************************
 * Fundamental operations
 ******************************************************************************/
struct VoronoiEdge* VoronoiDiagramGenerator::HEcreate(struct Edge *edge, int pm) {
  struct VoronoiEdge *answer;
  answer = new struct VoronoiEdge();
  answer->innerVedge = edge;
  answer->ELpm = pm;
  answer->PQnext = (struct VoronoiEdge *) NULL;
  answer->vertex = (struct Site *) NULL;
  return(answer);
}

// Return the next site
struct Site *VoronoiDiagramGenerator::nextone() {
  struct Site *index;
  if(siteIndex < siteNumber) {
    index = &sites[siteIndex];
    siteIndex += 1;
    return index;
  }
  else return (struct Site *) NULL;
}

void VoronoiDiagramGenerator::pushGraphEdge(double x1, double y1, double x2, double y2) {
  GraphEdge* newEdge = new GraphEdge;
  newEdge->next = allEdges;
  allEdges = newEdge;
  newEdge->x1 = x1;
  newEdge->y1 = y1;
  newEdge->x2 = x2;
  newEdge->y2 = y2;
}

/******************************************************************************
 * Edge List for all the edges on the plane
 ******************************************************************************/
bool VoronoiDiagramGenerator::EdgeListInit() {
  if(siteNumber == 0) return false;

  EdgeListLeftBorder = HEcreate( (struct Edge *)NULL, 0);
  EdgeListRightBorder = HEcreate( (struct Edge *)NULL, 0);
  
  EdgeListLeftBorder->leftVedge = (struct VoronoiEdge *) NULL;
  EdgeListLeftBorder->rightVedge = EdgeListRightBorder;
  EdgeListRightBorder->leftVedge = EdgeListLeftBorder;
  EdgeListRightBorder->rightVedge = (struct VoronoiEdge *)NULL;

  return true;
}

// Insert newVDedge on the right the current edge
void VoronoiDiagramGenerator::EdgeListInsert(struct VoronoiEdge *current, struct VoronoiEdge *newVDedge) {
  newVDedge->leftVedge = current;
  newVDedge->rightVedge = current->rightVedge;
  current->rightVedge->leftVedge = newVDedge;
  current->rightVedge = newVDedge;
}

struct VoronoiEdge *VoronoiDiagramGenerator::leftVoronoiEdge(struct Point *node) {
  // Linear-search of the Edgelist to find the left edge of node
  struct VoronoiEdge *index = EdgeListLeftBorder; // Start from the left end
  do {
    index = index->rightVedge;
  } while(index != EdgeListRightBorder && rightCheck(index, node));
  index = index->leftVedge;
  
  return index;
}

// This delete routine can't reclaim node, since pointers from hash table may be present.  
void VoronoiDiagramGenerator::EdgeListDelete(struct VoronoiEdge *VDedge) {
  VDedge->leftVedge->rightVedge = VDedge->rightVedge;
  VDedge->rightVedge->leftVedge = VDedge->leftVedge;
  VDedge->innerVedge = (struct Edge *) DELETED;
}


/******************************************************************************
 * Geometry operations
 ******************************************************************************/

std::vector<std::pair<double, double> > VoronoiDiagramGenerator::convexHullset(std::vector<std::pair<double, double> > viewAngleList) {
  // Andrew's monotone chain convex hull algorithm
  std::vector<std::pair<double, double> > boundary;
  int length = viewAngleList.size(), index = 0;
  if(length == 1) return viewAngleList;
  // Lexicographical sorting
  sort(viewAngleList.begin(), viewAngleList.end(), [](const std::pair<double, double> &a, const std::pair<double, double> &b) {
      return a.first < b.first || (a.first == b.first && a.second < b.second);
    });
  // Building the lower hull
  boundary.resize(2 * length);
  for(int i = 0; i < length; i++) {
    while(index >= 2 && orientation(boundary[index-2], boundary[index-1], viewAngleList[i]) <= EPS) index--;
    boundary[index++] = viewAngleList[i];
  }
  // Building the upper hull
  for(int i = length - 2, j = index+1; i >= 0; i--) {
    while(index >= j && orientation(boundary[index-2], boundary[index-1], viewAngleList[i]) <= EPS) index--;
    boundary[index++] = viewAngleList[i];
  }

  boundary.resize(index-1); // direction: clockwise
  
  return boundary;
}

int VoronoiDiagramGenerator::orientation(std::pair<double, double> p0, std::pair<double, double> a, std::pair<double, double> b) {
  return (a.first - p0.first) * (b.second - p0.second) - (a.second - p0.second) * (b.first - p0.first);
}

std::vector<std::pair<double, double> > VoronoiDiagramGenerator::convexHullExpand(std::vector<std::pair<double, double> > chBoundary, double moat) {
  // Input boudnary points should be clockwise of counterclockwise
  if(moat < EPS || chBoundary.size() < 3) return chBoundary;
  // Find an inner point in the convex hull;
  std::pair<double, double> innerPoint;
  innerPoint.first = ((chBoundary[0].first + chBoundary[1].first)*0.5 + chBoundary[2].first)*0.5;
  innerPoint.second = ((chBoundary[0].second + chBoundary[1].second)*0.5 + chBoundary[2].second)*0.5;

  std::vector<std::pair<double, double> > boundaryExpand;
  int length = chBoundary.size();
  for(int i = 0; i < length; i++) {
    std::pair<double, double> p1, p2, p3; // Three consecutive points
    p1 = chBoundary[i % length];
    p2 = chBoundary[(i+1) % length];
    p3 = chBoundary[(i+2) % length];
    
    double a1, b1, c1; // Expanded line
    a1 = -(p2.second - p1.second);
    b1 = p2.first - p1.first;
    c1 = p1.first * (p2.second - p1.second) - p1.second * (p2.first - p1.first);

    double newc1temp = c1 - sqrt(a1*a1 + b1*b1) * moat; // Alternative c1
    double newc2temp = c1 + sqrt(a1*a1 + b1*b1) * moat; // Alternative c2
    if(distPointToLineABC(innerPoint, a1, b1, newc1temp) < distPointToLineABC(innerPoint, a1, b1, newc2temp)) c1 = newc2temp;
    else c1 = newc1temp;

    double a2, b2, c2; // Expanded line
    a2 = -(p3.second - p2.second);
    b2 = p3.first - p2.first;
    c2 = p2.first * (p3.second - p2.second) - p2.second * (p3.first - p2.first);

    newc1temp = c2 - sqrt(a2*a2 + b2*b2) * moat; // Alternative c2
    newc2temp = c2 + sqrt(a2*a2 + b2*b2) * moat; // Alternative c2
    if(distPointToLineABC(innerPoint, a2, b2, newc1temp) < distPointToLineABC(innerPoint, a2, b2, newc2temp)) c2 = newc2temp;
    else c2 = newc1temp;
    // Calculate the intersection of two expanded lines
    std::pair<double, double> intersection;
    if((a1*(c2*b1 - c1*b2) - b1*(c2*a1 - c1*a2)) < EPS && (a1*(c2*b1 - c1*b2) - b1*(c2*a1 - c1*a2)) > -EPS) intersection.first = p2.first;
    else intersection.first = -c1 * (c2*b1 - c1*b2) / (a1*(c2*b1 - c1*b2) - b1*(c2*a1 - c1*a2));
    if((b1*(c2*a1 - c1*a2) - a1*(c2*b1 - c1*b2)) < EPS && (b1*(c2*a1 - c1*a2) - a1*(c2*b1 - c1*b2)) > -EPS) intersection.second = p2.second;
    else intersection.second = -c1 * (c2*a1 - c1*a2) / (b1*(c2*a1 - c1*a2) - a1*(c2*b1 - c1*b2));

    boundaryExpand.push_back(intersection);
  }

  return boundaryExpand;
}


double VoronoiDiagramGenerator::distPointToLineABC(std::pair<double, double> innerPoint, double a, double b, double c) {
  return std::fabs((a * innerPoint.first + b * innerPoint.second + c)) / sqrt(a*a + b*b);
}


struct Site * VoronoiDiagramGenerator::leftSite(struct VoronoiEdge *VDedge) {
  if(VDedge->innerVedge == (struct Edge *)NULL) return bottomsite;
  return VDedge->ELpm == LEFTedge ? VDedge->innerVedge->siteSeg[LEFTedge] : VDedge->innerVedge->siteSeg[RIGHTedge];
}

struct Site *VoronoiDiagramGenerator::rightSite(struct VoronoiEdge *VDedge) {
  // If this VDedge has no edge, return the bottom site (whatever that is)
  if(VDedge->innerVedge == (struct Edge *)NULL) return bottomsite;
  // If the ELpm field is zero, return the site 0 that this edge bisects,
  // otherwise return site number 1
  return VDedge->ELpm == LEFTedge ? VDedge->innerVedge->siteSeg[RIGHTedge] : VDedge->innerVedge->siteSeg[LEFTedge] ;
}

struct Edge * VoronoiDiagramGenerator::generateBisector(struct Site *s1, struct Site *s2) {
  struct Edge *newedge = new struct Edge();
  
  newedge->siteSeg[0] = s1; // Store the sites that this edge is bisecting
  newedge->siteSeg[1] = s2;
  usedMark(s1); // Mark the sites are used
  usedMark(s2);

  // To begin with, there are no endpoints on the bisector - it goes to infinity
  newedge -> bisectSeg[0] = (struct Site *) NULL; 
  newedge -> bisectSeg[1] = (struct Site *) NULL;
  // Get the difference in x dist between the sites
  double dx = s2->coord.x - s1->coord.x; 
  double dy = s2->coord.y - s1->coord.y;
  // Make sure that the difference in positive
  double adx = dx > 0 ? dx : -dx; 
  double ady = dy > 0 ? dy : -dy;
  // The line function is ax + by = c
  newedge->c = (double)(s1->coord.x * dx + s1->coord.y * dy + (dx*dx + dy*dy)*0.5);

  if (adx > ady) {
    newedge->a = 1.0;
    newedge->b = dy/dx;
    newedge->c /= dx; // Set formula of line, with x fixed to 1
  } else {
    newedge->b = 1.0;
    newedge->a = dx/dy;
    newedge->c /= dy; // Set formula of line, with y fixed to 1
  }
  newedge->edgenbr = edgeNumber; // mark the index of this new edge
  edgeNumber += 1;
  return newedge;
}

// Create a new site where the VDedge1 and VDedge2 intersect
// note that the Point in the argument list is not used, don't know why it's there
struct Site * VoronoiDiagramGenerator::generateIntersection(struct VoronoiEdge *VDedge1, struct VoronoiEdge *VDedge2) {
  struct Edge *e1 = VDedge1->innerVedge;
  struct Edge *e2 = VDedge2->innerVedge;
  // Check whether both sides have the edge
  if(e1 == (struct Edge*) NULL || e2 == (struct Edge*) NULL) return ((struct Site *) NULL); 

  // If the two edges bisect the same parent (same focal site), return
  if (e1->siteSeg[1] == e2->siteSeg[1]) return ((struct Site *) NULL);
  
  double crossProduct = e1->a * e2->b - e1->b * e2->a; // cross product
  if (-EPS < crossProduct && crossProduct < EPS) return ((struct Site *) NULL);
  
  double xint = (e1->c * e2->b - e2->c * e1->b)/crossProduct;
  double yint = (e2->c * e1->a - e1->c * e2->a)/crossProduct;
  struct Edge *edge;
  struct VoronoiEdge *VDedgeSelect;
  if((e1->siteSeg[1]->coord.y < e2->siteSeg[1]->coord.y) ||
     (e1->siteSeg[1]->coord.y == e2->siteSeg[1]->coord.y &&
      e1->siteSeg[1]->coord.x < e2->siteSeg[1]->coord.x)) {
    VDedgeSelect = VDedge1;
    edge = e1;
  } else {
    VDedgeSelect = VDedge2;
    edge = e2;
  }
  int right_of_site = xint >= edge->siteSeg[1]->coord.x;
  if ((right_of_site && VDedgeSelect->ELpm == LEFTedge) ||
      (!right_of_site && VDedgeSelect->ELpm == RIGHTedge)) return ((struct Site *) NULL);
  
  // Create a new site at the point of intersection - this is a new vector event waiting to happen
  struct Site *futureIntersectionVertex = new struct Site();
  futureIntersectionVertex->visited = 0;
  futureIntersectionVertex->coord.x = xint;
  futureIntersectionVertex->coord.y = yint;
  return futureIntersectionVertex;
}

// Returns 1 if node is on the right of VDedge
int VoronoiDiagramGenerator::rightCheck(struct VoronoiEdge *VDedge, struct Point *node) {
  struct Edge *edge = VDedge->innerVedge;
  struct Site *topsite = edge->siteSeg[1];
  
  int right_of_site = node->x > topsite->coord.x;
  if(right_of_site && VDedge->ELpm == LEFTedge) return 1;
  if(!right_of_site && VDedge->ELpm == RIGHTedge) return 0;
  
  int fast = 0, above;
  if (edge->a == 1.0) {
    double dyp = node->y - topsite->coord.y;
	double dxp = node->x - topsite->coord.x;
	if((!right_of_site && (edge->b < 0.0)) || (right_of_site && (edge->b >= 0.0))) {
      above = dyp >= edge->b * dxp;	
      fast = above;
	} else {
      above = node->x + node->y * edge->b > edge->c;
      if(edge->b<0.0) above = !above;
      if(!above) fast = 1;
	}
	if(!fast) {
      double dxs = topsite->coord.x - edge->siteSeg[0]->coord.x;
      above = edge->b * (dxp*dxp - dyp*dyp) < dxs*dyp*(1.0+2.0*dxp/dxs + edge->b * edge->b);
      if(edge->b < 0.0) above = !above;
	}
  } else { //edge->b == 1.0 
    double yl = edge->c - edge->a * node->x;
	double t1 = node->y - yl;
	double t2 = node->x - topsite->coord.x;
	double t3 = yl - topsite->coord.y;
	above = t1*t1 > t2*t2 + t3*t3;
  }
  return (VDedge->ELpm == LEFTedge ? above : !above);
}

/******************************************************************************
 * Priority queue for the sites and intersections on the plane
 ******************************************************************************/
bool VoronoiDiagramGenerator::PQinit(){
  PQsize = 0;
  if(siteNumber == 0) return false;
  PQtable = new struct VoronoiEdge();

  return true;
}

int VoronoiDiagramGenerator::PQempty() {
  return PQsize == 0;
}

// Push the ArcEdge in the priority queue
void VoronoiDiagramGenerator::PQinsert(struct VoronoiEdge *current, struct Site * v, double offset) {
  current->vertex = v;
  usedMark(v); // v is used
  current->ystar = (double)(v->coord.y + offset); // mapping *(z)
  struct VoronoiEdge *last = PQtable;
  struct VoronoiEdge *next;
  // Find the right position for current to keep the order
  while ((next = last->PQnext) != (struct VoronoiEdge *) NULL &&
         (current->ystar > next->ystar ||
          (current->ystar == next->ystar && v->coord.x > next->vertex->coord.x))) {
    last = next;
  };
  current->PQnext = last->PQnext;
  last->PQnext = current;
  PQsize += 1;
}

// Remove the ArcEdge PQtable
void VoronoiDiagramGenerator::PQdelete(struct VoronoiEdge *VDedge) {
  if(VDedge->vertex != (struct Site *) NULL) {
    struct VoronoiEdge *index = PQtable;
    
    while (index->PQnext != VDedge) index = index->PQnext;
    index->PQnext = VDedge->PQnext;
    PQsize -= 1;
    unusedMark(VDedge->vertex);
    VDedge->vertex = (struct Site *) NULL;
  }
}

struct VoronoiEdge *VoronoiDiagramGenerator::PQpopMin() {
  struct VoronoiEdge *curr = PQtable->PQnext;
  PQtable->PQnext = curr->PQnext;
  PQsize -= 1;
  
  return curr;
}

struct Point VoronoiDiagramGenerator::PQtop() {
  struct Point minPoint;
  minPoint.x = PQtable->PQnext->vertex->coord.x;
  minPoint.y = PQtable->PQnext->ystar;
  
  return minPoint;
}


/******************************************************************************
 * Additional operations
 ******************************************************************************/
void VoronoiDiagramGenerator::endPoint(struct Edge *edge, int pos, struct Site *st) {
  edge->bisectSeg[pos] = st;
  usedMark(st);
  if(edge->bisectSeg[RIGHTedge - pos]== (struct Site *) NULL) return;

  VDedgeGenerator(edge);

  unusedMark(edge->siteSeg[LEFTedge]);
  unusedMark(edge->siteSeg[RIGHTedge]);
}

double VoronoiDiagramGenerator::distance(struct Site *s1, struct Site *s2) {
  double dx, dy;
  dx = s1->coord.x - s2->coord.x;
  dy = s1->coord.y - s2->coord.y;
  return (double)(sqrt(dx*dx + dy*dy));
}


void VoronoiDiagramGenerator::generateVDvertex(struct Site *st) {
  st->sitemarker = VDverticesNumber;
  VDverticesNumber += 1;
}

void VoronoiDiagramGenerator::unusedMark(struct Site *st) {
  st->visited -= 1;
}

void VoronoiDiagramGenerator::usedMark(struct Site *st) {
  st->visited += 1;
}

void VoronoiDiagramGenerator::VDedgeGenerator(struct Edge *VDedge) {
  double x1 = VDedge->siteSeg[0]->coord.x;
  double x2 = VDedge->siteSeg[1]->coord.x;
  double y1 = VDedge->siteSeg[0]->coord.y;
  double y2 = VDedge->siteSeg[1]->coord.y;

  // Ignore the Voronoi Diagram edge is two sites are too close
  if(sqrt(((x2 - x1) * (x2 - x1)) + ((y2 - y1) * (y2 - y1))) < gapThreshold) return;
  
  double pxmin = borderMinX;
  double pxmax = borderMaxX;
  double pymin = borderMinY;
  double pymax = borderMaxY;

  struct Site *s1, *s2; // Voronoi Diagram vertices
  if(VDedge->a == 1.0 && VDedge->b >= 0.0) {
    s1 = VDedge->bisectSeg[1];
    s2 = VDedge->bisectSeg[0];
  } else {
    s1 = VDedge->bisectSeg[0];
    s2 = VDedge->bisectSeg[1];
  }
  
  if(VDedge->a == 1.0) {
    y1 = pymin;
    if (s1 != (struct Site *)NULL && s1->coord.y > pymin) y1 = s1->coord.y;
    if(y1 > pymax) y1 = pymax;
    x1 = VDedge->c - VDedge->b * y1;
    
    y2 = pymax;
    if (s2 != (struct Site *)NULL && s2->coord.y < pymax) y2 = s2->coord.y;
    if(y2 < pymin) y2 = pymin;
    x2 = VDedge->c - VDedge->b * y2;
    
    if (((x1 > pxmax) && (x2 > pxmax)) || ((x1 < pxmin) && (x2 < pxmin))) return;
    
    if(x1 > pxmax) {
      x1 = pxmax;
      y1 = (VDedge->c - x1)/VDedge->b;
    }
    if(x1 < pxmin) {
      x1 = pxmin;
      y1 = (VDedge->c - x1)/VDedge->b;
    }
    if(x2 > pxmax) {
      x2 = pxmax;
      y2 = (VDedge->c - x2)/VDedge->b;
    }
    if(x2 < pxmin) {
      x2 = pxmin;
      y2 = (VDedge->c - x2)/VDedge->b;
    }
  } else {
    x1 = pxmin;
    if (s1 != (struct Site *)NULL && s1->coord.x > pxmin) x1 = s1->coord.x;
    if(x1 > pxmax) x1 = pxmax;
    y1 = VDedge->c - VDedge->a * x1;

    x2 = pxmax;
    if (s2 != (struct Site *)NULL && s2->coord.x < pxmax) x2 = s2->coord.x;
    if(x2 < pxmin) x2 = pxmin;
    y2 = VDedge->c - VDedge->a * x2;
    
    if (((y1 > pymax) && (y2 > pymax)) || ((y1 < pymin) && (y2 < pymin))) return;
    
    if(y1 > pymax) {
      y1 = pymax;
      x1 = (VDedge->c - y1)/VDedge->a;
    }
    if(y1 < pymin) {
      y1 = pymin;
      x1 = (VDedge->c - y1)/VDedge->a;
    }
    if(y2 > pymax) {
      y2 = pymax;
      x2 = (VDedge->c - y2)/VDedge->a;
    }
    if(y2 < pymin) {
      y2 = pymin;
      x2 = (VDedge->c - y2)/VDedge->a;
    }
  }
  pushGraphEdge(x1, y1, x2, y2);

  std::pair<struct Point, struct Point> add;
  add.first.x = x1;
  add.first.y = y1;
  add.second.x = x2;
  add.second.y = y2;
  VDedgeSet.push_back(add);
  
  std::pair<struct Site, struct Site> siteNum; 
  siteNum.first = *VDedge->siteSeg[0];
  siteNum.second = *VDedge->siteSeg[1];
  VDedgeSetHelper.push_back(siteNum);
  
}

/******************************************************************************
 * There is an important mapping here: *(z)=(z_x, z_y+d(z)) where d(z) is the
 * Euclidean distance from z to the nearest site.
 * The edges, regions, vertices are under such a mapping.
 ******************************************************************************/
bool VoronoiDiagramGenerator::voronoiOperation() {
  // Initialize the priority queue of VoronoiEdge.
  PQinit();
  // Build the bottom (basic) site based on the 1st incoming site.
  bottomsite = nextone();
  // Initialize the hashTable of Edges.
  bool retval = EdgeListInit();
  if(!retval) return false; 
	
  struct Site *incomingSite = nextone(); // Build the new site to process
  
  while(1) {
    struct Point newPopPoint;
    if(!PQempty()) newPopPoint = PQtop(); // Find the lowest point (Geometric) in PQtable
    /* Site mission:
     * If the lowest site has a smaller y value than the lowest
     * vector intersection, process the site */
    if (incomingSite != (struct Site *) NULL &&
        (PQempty() || incomingSite->coord.y < newPopPoint.y ||
         (incomingSite->coord.y == newPopPoint.y &&
          incomingSite->coord.x < newPopPoint.x))) {
      // 1. Find the region (two VoronoiEdges) contineing the incomingsite */
      // Get the left VDedge of the incomingSite
      struct VoronoiEdge *leftVDedge = leftVoronoiEdge(&(incomingSite->coord));
      // Get the first VDedge to the RIGHT of the new site
      struct VoronoiEdge *rightVDedge = leftVDedge->rightVedge;
      
      // 2. Create bisector
      // If this VDedge has no edge, bot = bottomsite (whatever that is)
      struct Site *bot = rightSite(leftVDedge);
      // Create a new edge that bisects the bot and incomingSite
      struct Edge *siteEdge = generateBisector(bot, incomingSite); 
      // Create a new VDedge (bisector), setting its ELpm field to 0
      struct VoronoiEdge *bisector = HEcreate(siteEdge, LEFTedge);

      // 3. Update EdgeList
      // 3.1 Insert this new bisector edge between the left and right vectors in a linked list
      EdgeListInsert(leftVDedge, bisector);
      // Generate the new intersection of the left VDedge and the bisector
      struct Site *intersectionVertex = generateIntersection(leftVDedge, bisector);
      // If the new bisector intersects with the left edge, remove
      // the left edge's vertex, and put in the new one
      if (intersectionVertex != (struct Site *) NULL) { 
        PQdelete(leftVDedge);
        PQinsert(leftVDedge, intersectionVertex, distance(intersectionVertex, incomingSite));
      }
      // 3.2 Move left VDedge to be the new created bisector, which is the leftside of right VDedge 
      leftVDedge = bisector;
      // Create a new bisector with ELpm to be 1
      bisector = HEcreate(siteEdge, RIGHTedge);
      // Insert the new bisector to the right of the original bisector earlier
      EdgeListInsert(leftVDedge, bisector); 
      intersectionVertex = generateIntersection(bisector, rightVDedge);
      // If this new bisector intersects with the right VDedge
      if (intersectionVertex != (struct Site *) NULL) {
        // Push the new VDedge into the ordered linked list of vertices
        PQinsert(bisector, intersectionVertex, distance(intersectionVertex, incomingSite)); 
      }
      incomingSite = nextone(); // Move to the next site of intersection.
    }
    /* Voronoi Diagram vertex (intersection) mission */
    else if (!PQempty()) {
      // 1. Intersection is the smallest one
      struct VoronoiEdge *VDvertex = PQpopMin(); // lowest ordered item
      struct VoronoiEdge *leftVDedgeVDv = VDvertex->leftVedge;
      struct VoronoiEdge *rightVDedgeVDv = VDvertex->rightVedge;
      struct VoronoiEdge *RrightVDedgeVDv = rightVDedgeVDv->rightVedge;
      // Get the site on the left of the current VDvertex
      struct Site *bot = leftSite(VDvertex);
      // Get the right of the right of the current VDvertex
      struct Site *top = rightSite(rightVDedgeVDv);
      // Get the current vertex caused VDvertex
      struct Site *st = VDvertex->vertex;
      // 2. Operation part
      // 2.1 Mark the vertex number (can not do it in the above IF part,
      // because it might be processed again)
      generateVDvertex(st);
      // Mark st as the right end point of VDvertex as the termination
      endPoint(VDvertex->innerVedge, VDvertex->ELpm, st);
      // Mark st as the left end point of rightVDvertex
      endPoint(rightVDedgeVDv->innerVedge,rightVDedgeVDv->ELpm, st);
      // Delete the current intersection (or site) from the EdgeList,
      // can't delte yet because there might be pointers to it
      EdgeListDelete(VDvertex);
      // Delte the right vertex of current VDedgev from the priority queue
      PQdelete(rightVDedgeVDv);
      // Delete the right intersection (or site) of current from the EdgeList,
      EdgeListDelete(rightVDedgeVDv);
      int pm = LEFTedge; //set the pm variable to zero
      // If the site to the left of the event is higher than the Site to the
      // right of it, then swap them and set the 'pm' variable to 1
      if (bot->coord.y > top->coord.y) {
        std::swap(top, bot);
        pm = RIGHTedge;
      }
      // 2.2 Create an Edge (or line) that is between the two Sites.
      // This creates the formula of the line, and assigns a line number to it
      struct Edge *bottopEdge = generateBisector(bot, top);
      // Create a VDedge from the bottomEdge, and make it point to that edge with its innerVedge field
      struct VoronoiEdge *bisector = HEcreate(bottopEdge, pm);
      // Insert the new bisector to the right of the left VDedgeVDv
      EdgeListInsert(leftVDedgeVDv, bisector);
      // Set one endpoint to the new edge to be the vector point st
      endPoint(bottopEdge, RIGHTedge - pm, st);
      // 2.3 If the site to the left of this bisector is higher than the right
      // site, then this endpoint is put in position 0; otherwise in pos 1
      unusedMark(st); // Delete the vector 'v'
      // If left VDedge and the new bisector don't intersect, then delete the left one, and reinsert it
      struct Site *intersectionVertex = generateIntersection(leftVDedgeVDv, bisector);
      if(intersectionVertex != (struct Site *) NULL) {	
        PQdelete(leftVDedgeVDv);
        PQinsert(leftVDedgeVDv, intersectionVertex, distance(intersectionVertex, bot));
      }
      // If right VDedge and the new bisector don't intersect, then reinsert it
      intersectionVertex = generateIntersection(bisector, RrightVDedgeVDv);
      if (intersectionVertex != (struct Site *) NULL) {	
        PQinsert(bisector, intersectionVertex, distance(intersectionVertex, bot));
      }
      
    }
    else break;
  }

  for(struct VoronoiEdge *it = EdgeListLeftBorder->rightVedge;
      it != EdgeListRightBorder; it = it->rightVedge) {
    VDedgeGenerator(it->innerVedge);
  }

  return true;	
}



};
};
};



