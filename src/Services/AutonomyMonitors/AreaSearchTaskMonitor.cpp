#include "AutonomyMonitors/AreaSearchTaskMonitor.h"

#include "iostream"
#include <tuple>
#include "afrl/cmasi/Location3D.h"
#include "afrl/cmasi/autonomymonitor/TaskSuccess.h"
#include "afrl/cmasi/autonomymonitor/TaskFailure.h"
#include "afrl/cmasi/autonomymonitor/TaskMonitorStarted.h"
#include "afrl/cmasi/AbstractGeometry.h"
#include "afrl/cmasi/AbstractGeometryDescendants.h"
#include "AutonomyMonitors/GeometryUtilities.h"
#include "AutonomyMonitors/MonitorUtils.h"

#include "AutonomyMonitors/VoronoiDiagramGenerator.h"


namespace uxas {
namespace service {
namespace monitoring {
  
  AreaSearchTaskMonitor::AreaSearchTaskMonitor(AutonomyMonitorServiceMain * service_ptr, 
    std::shared_ptr<afrl::cmasi::AreaSearchTask> areaSearchTask):MonitorBase(service_ptr), _task(areaSearchTask) {
    this->debug = true;
    if(this->debug) {
      std::cout << "[AreaSearchTaskID: " << this->_task->getTaskID() << "]" << std::endl;
      // Get the search area type
      afrl::cmasi::AbstractGeometry* const areaGeometry = this->_task->getSearchArea();
      // is a cicle
      auto circle = dynamic_cast<afrl::cmasi::Circle*>(areaGeometry); 
      if(circle) {
        std::cout << "  [SearchAreaType: " << circle->TypeName << std::endl;
        std::cout << "     Center: " << circle->getCenterPoint()->getLatitude()
                  << ", " << circle->getCenterPoint()->getLongitude() << std::endl;
        std::cout << "     Radius: " << circle->getRadius() << std::endl;
      }
      // is a polygon
      auto poly = dynamic_cast<afrl::cmasi::Polygon*>(areaGeometry);
      if(poly) {
        std::cout << "  [SearchAreaType: " << poly->TypeName << std::endl;
        std::cout << "     Boundarypoints: " << std::endl;
        std::vector<afrl::cmasi::Location3D*> ptList = poly->getBoundaryPoints();
        for(auto loc: ptList) {
          std::cout << loc->getLatitude() << ", " << loc->getLongitude() << std::endl;
        }
      }
      // is a rectangle
      auto rect = dynamic_cast<afrl::cmasi::Rectangle*>(areaGeometry);
      if(rect) {
        std::cout << "  [SearchAreaType: " << rect->TypeName << std::endl;
        std::cout << "     Center: " << rect->getCenterPoint()->getLatitude()
                  << ", " << rect->getCenterPoint()->getLongitude() << std::endl;
        std::cout << "     Width: " << rect->getWidth() << ", " << "Height: " << rect->getHeight() << std::endl;
      }
    }
    
    sendMonitorStartMessage();
  };

  AreaSearchTaskMonitor::~AreaSearchTaskMonitor(){};

  void AreaSearchTaskMonitor::addVehicleStateMessage(VehicleStateMessage const & vMessage){
    auto const &cFoot = vMessage.getCameraFootprint();
    std::vector<std::pair<double, double>> areaCoordinates;
    // check the accessibility of the camera angle
    if(vMessage.checkCameraAngleInWedge(this->_task->getViewAngleList())) {
      // change the lat/long to north/east and store them in anglelist_m
      std::vector<std::pair<double, double>> angleList_m;
      for(auto loc: cFoot) {
        auto xy_loc = get_east_north_coordinates(this->flatEarth, loc.get());
        angleList_m.push_back(xy_loc);
      }
      
      // Based on the view angle list, generate the Voronoi diagram
      // input: the points of view angle lsit,
      // output: voronoi vertices
      bool isSearched = true;
      
      // Different AreaSearchTask corresponds to different boundarypoints
      afrl::cmasi::AbstractGeometry* const areaGeometry = this->_task->getSearchArea();
      // is a rectangle
      auto rect = dynamic_cast<afrl::cmasi::Rectangle*>(areaGeometry);
      if(rect) {
        auto center = get_east_north_coordinates(flatEarth, rect->getCenterPoint());
        double height = double(rect->getHeight());
        double width = double(rect->getWidth());
        
        VoronoiDiagramGenerator vdg;
        vdg.generateVDrectangle(angleList_m, center.first - width/2.0, center.first + width/2.0, center.second - height/2.0, center.second + height/2.0, 0);
        vdg.hashTableOfSiteVDvertices();
        // The Voronoi Diagram checking for each VD area
        for(auto item: vdg.sites) {
          bool siteSearch = true;
          for(int i = 0; i < vdg.VDvertices[item.sitemarker].size(); i++) {
            double dist = sqrt(pow(vdg.VDvertices[item.sitemarker][i].x - item.coord.x, 2) + pow(vdg.VDvertices[item.sitemarker][i].y - item.coord.y, 2));
            if(dist > this->innerCircleRadius) {
              siteSearch = false;
              break;
            }
          }
          if(!siteSearch) {
            isSearched = false;
            break;
          }
        }
        // The expanded convex hull area check
        std::vector<std::pair<double, double> > convexHull = vdg.convexHullset(angleList_m);
        std::vector<std::pair<double, double> > expandCH = vdg.convexHullExpand(convexHull, this->ExpandMoat);
        
        if(isSearched) {
          MonitorPolygon boundaryECH (expandCH);
          double distToViolation;
          bool insidePoly;
          std::vector<std::pair<double, double> > areaBoundary;
          areaBoundary.push_back({center.first - width/2.0, center.second + height/2.0});
          areaBoundary.push_back({center.first + width/2.0, center.second + height/2.0});
          areaBoundary.push_back({center.first + width/2.0, center.second - height/2.0});
          areaBoundary.push_back({center.first - width/2.0, center.second - height/2.0});
          distToViolation = std::fmin(width/2.0, height/2.0);
          for(auto item: areaBoundary) {
            std::tie(insidePoly, distToViolation) = boundaryECH.isMember(item.first, item.second);
            if(!insidePoly) {
              isSearched = false;
              break;
            }
          }
        }
        
      }
      
      // is a circle
      auto circle = dynamic_cast<afrl::cmasi::Circle*>(areaGeometry);
      if(circle) {
        auto center = get_east_north_coordinates(flatEarth, circle->getCenterPoint());
        double radius = circle->getRadius();
        
        VoronoiDiagramGenerator vdg;
        vdg.generateVDcircle(angleList_m, center, radius);
        vdg.hashTableOfSiteVDvertices();
        // The Voronoi Diagram checking for each VD area
        for(auto item: vdg.sites) {
          bool siteSearch = true;
          for(int i = 0; i < vdg.VDvertices[item.sitemarker].size(); i++) {
            double dist = sqrt(pow(vdg.VDvertices[item.sitemarker][i].x - item.coord.x, 2) + pow(vdg.VDvertices[item.sitemarker][i].y - item.coord.y, 2));
            if(dist > this->innerCircleRadius) {
              siteSearch = false;
              break;
            }
          }
          if(!siteSearch) {
            isSearched = false;
            break;
          }
        }
        // The expanded convex hull area check
        std::vector<std::pair<double, double> > convexHull = vdg.convexHullset(angleList_m);
        std::vector<std::pair<double, double> > expandCH = vdg.convexHullExpand(convexHull, this->ExpandMoat);
        if(isSearched) {
          int length = expandCH.size();
          for(int i = 0; i < length; i++) {
            std::pair<double, double> p1 = expandCH[i];
            std::pair<double, double> p2 = expandCH[(i+1) % length];
            double dist = std::fabs((p2.second - p1.second)*center.first - (p2.first - p1.first)*center.second + p2.first*p1.second - p2.second*p1.first) / sqrt(pow(p2.second - p1.second, 2) + pow(p2.first - p1.first, 2));
            if(dist < radius) {
              isSearched = false;
              break;
            }
          }
        }
        
      }
      
      // is a polygon
      auto poly = dynamic_cast<afrl::cmasi::Polygon*>(areaGeometry);
      if(poly) {
        std::vector<std::pair<double, double> > polyBoundary;
        std::vector<afrl::cmasi::Location3D*> ptList = poly->getBoundaryPoints();
        for(auto loc: ptList) {
          auto item = get_east_north_coordinates(flatEarth, loc);
          polyBoundary.push_back(item);
        }
        polyBoundary.push_back(polyBoundary.front());
        
        VoronoiDiagramGenerator vdg;
        vdg.generateVDpolygon(angleList_m, polyBoundary);
        vdg.hashTableOfSiteVDvertices();
        // The Voronoi Diagram checking for each VD area
        for(auto item: vdg.sites) {
          bool siteSearch = true;
          for(int i = 0; i < vdg.VDvertices[item.sitemarker].size(); i++) {
            double dist = sqrt(pow(vdg.VDvertices[item.sitemarker][i].x - item.coord.x, 2) + pow(vdg.VDvertices[item.sitemarker][i].y - item.coord.y, 2));
            if(dist > this->innerCircleRadius) {
              siteSearch = false;
              break;
            }
          }
          if(!siteSearch) {
            isSearched = false;
            break;
          }
        }
        // The expanded convex hull area check
        std::vector<std::pair<double, double> > convexHull = vdg.convexHullset(angleList_m);
        std::vector<std::pair<double, double> > expandCH = vdg.convexHullExpand(convexHull, this->ExpandMoat);

        if(isSearched) {
          MonitorPolygon boundaryECH (expandCH);
          double distToViolation;
          bool insidePoly;
          for(auto item: polyBoundary) {
            distToViolation = std::fmin(item.first, item.second);
            std::tie(insidePoly, distToViolation) = boundaryECH.isMember(item.first, item.second);
            if(!insidePoly) {
              isSearched = false;
              break;
            }
          }
        }
        
        
      }
      
      if(isSearched == false) std::cout << "WARNING!!! Mission failed!!!" << std::endl;
      
    } else { // if no carera angles, print error messages if debug is working
      if(this->debug) {
        UXAS_LOG_WARN("[AreaSearchTaskMonitor]: Camera Angles are not acceptable for taskID: ",
                      this->_task->getTaskID(), " vehicleID: ", vMessage.getVehicleID(),
                      " state messge at time: ", vMessage.getTimeStamp());
        UXAS_LOG_WARN("[AreaSearchTaskMonitor]: Camera angels azimuth: ",
                      vMessage.getCameraAzimuth(), " elevation: ", vMessage.getCameraElevation());
      }
    }
  }

  void AreaSearchTaskMonitor::sendMonitorStartMessage(){
    // Do not send until implemented.
  }

  bool AreaSearchTaskMonitor::isPropertySatisfied(){
    return true;
  }

  double AreaSearchTaskMonitor::propertyRobustness(){
    return 0.0;
  }
  
}
}
}
