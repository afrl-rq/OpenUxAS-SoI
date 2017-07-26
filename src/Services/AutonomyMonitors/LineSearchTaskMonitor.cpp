#include "AutonomyMonitors/LineSearchTaskMonitor.h"

#include <iostream>
#include "afrl/cmasi/Location3D.h"
#include "AutonomyMonitors/GeometryUtilities.h"
#include "AutonomyMonitors/MonitorUtils.h"
#include "afrl/cmasi/autonomymonitor/TaskSuccess.h"
#include "afrl/cmasi/autonomymonitor/TaskFailure.h"
#include "afrl/cmasi/autonomymonitor/LineSearchTaskFailure.h"
#include "afrl/cmasi/autonomymonitor/TaskMonitorStarted.h"
namespace uxas {
namespace service {
namespace monitoring {
using afrl::cmasi::Location3D;
using afrl::cmasi::LineSearchTask;

LineSearchTaskMonitor::LineSearchTaskMonitor(AutonomyMonitorServiceMain * service_ptr,
    std::shared_ptr<LineSearchTask> lineSearchTask): MonitorBase(service_ptr),
  _task(lineSearchTask) {
  // SRIRAM: Turn this on while developing
  this -> debug = true;
  // 1. Process the line into segments so that we can monitor the status of each segment
  std::vector<Location3D*> const & segmentList = lineSearchTask -> getPointList();
  int n = segmentList.size();
  if ( n < 2) {
    UXAS_LOG_WARN("[AutonomyMonitor]: LineSearchTaskMonitor. Task ID ", lineSearchTask -> getTaskID(), " has too few points in the line segment. ");
  }
  for (int i = 0; i < n - 1; ++i) {
    Location3D const * lA = segmentList[i];
    Location3D const * lB = segmentList[i + 1];
    auto east_north_A = get_east_north_coordinates(this -> flatEarth, lA);
    auto east_north_B = get_east_north_coordinates(this -> flatEarth, lB);
    /*-- Avoid large floating point errors by converting to north east coordinates relative to a start point --*/
    LineSegment ls(i, east_north_A.first, east_north_A.second, east_north_B.first, east_north_B.second);
    ls.setDebug(this -> debug);
    this -> segments.push_back( ls );
  }
  sendMonitorStartMessage();
};

LineSearchTaskMonitor::~LineSearchTaskMonitor() {};

void LineSearchTaskMonitor::sendMonitorStartMessage() {
  auto fObj = std::make_shared<afrl::cmasi::autonomymonitor::TaskMonitorStarted>();
  fObj -> setTaskID( this -> _task -> getTaskID());
  service_ -> broadcastMessage(fObj);
}

void LineSearchTaskMonitor::addVehicleStateMessage(VehicleStateMessage const & vMessage) {
  auto const & cFoot = vMessage.getCameraFootprint();
  std::vector< std::pair<double, double> > polygonCoordinates;
  // First check if the camera angle is acceptable
  if (vMessage.checkCameraAngleInWedge(_task -> getViewAngleList())) {
    for (auto loc : cFoot) {
      auto xy_loc = get_east_north_coordinates(this-> flatEarth, loc.get());
      polygonCoordinates.push_back(xy_loc);
    }

    MonitorPolygon footPrint (polygonCoordinates);
    for (auto & ls : segments) {
      if (!ls.isSegmentCovered()) {
        ls.registerSensorFootprint(footPrint);
      }
    }
  } else {
    UXAS_LOG_WARN("[LineSearchTaskMonitor]: Camera angles are not acceptable for task ID:", _task -> getTaskID(), " vehicle ID:", vMessage.getVehicleID(), " state message at time : ", vMessage.getTimeStamp());
    UXAS_LOG_WARN("[LineSearchTaskMonitor]: camera angles azimuth: ", vMessage.getCameraAzimuth(), " elevation: " , vMessage.getCameraElevation() );
  }
  return;
}


bool LineSearchTaskMonitor::isPropertySatisfied() {
  for (auto & ls : this -> segments) {
    if (!ls.isSegmentCovered())
      return false;
  }
  return true;
}

double LineSearchTaskMonitor::propertyRobustness() {
  return _robustness;
}

void LineSearchTaskMonitor::sendTaskStatus() {
  _robustness = 10000.0;
  for (auto const & ls: segments){
    _robustness = std::min(_robustness, ls.getRobustness());
  }

  if (debug) {
    std::cout << "[LineSearchTaskMonitor]: Got task status request. " << std::endl;
    for (auto & ls : this -> segments) {
      ls.printIntervals();
      if (!ls.isSegmentCovered()) {
        UXAS_LOG_WARN("[LineSearchTaskMonitor]: Segment ID: ", ls.getID(), " failed." );
      } else {
        UXAS_LOG_INFORM("[LineSearchTaskMonitor]: Segment ID: ", ls.getID(), " succeeded." );
      }
      UXAS_LOG_INFORM("[LineSearchTaskMonitor]: Robustness Calculated = ", _robustness);
    }
  }

  if (isPropertySatisfied()) {
    if (debug) { std::cout << "[LineSearchTaskMonitor]: SUCCESS with robutsness: " << _robustness << std::endl; }

    auto fObj = std::make_shared<afrl::cmasi::autonomymonitor::TaskSuccess>();
    fObj -> setTaskID(this -> _task -> getTaskID() );
    fObj -> setRobustness(_robustness);
    service_ -> broadcastMessage(fObj);
  } else {
    if (debug) {
      std::cout << "[LineSearchTaskMonitor]: FAILURE with robutsness: " << _robustness << std::endl;
    }
    auto fObj = std::make_shared<afrl::cmasi::autonomymonitor::LineSearchTaskFailure>();
    fObj -> setTaskID(this -> _task -> getTaskID());
    fObj -> setRobustness(_robustness);
    std::vector<int64_t> & missedSegments = fObj -> getMissedSegments();
    for (auto const & ls: this -> segments){
      if (!ls.isSegmentCovered())
        missedSegments.push_back(ls.getID());
    }
    service_ -> broadcastMessage(fObj);
  }
}

}
}
}
