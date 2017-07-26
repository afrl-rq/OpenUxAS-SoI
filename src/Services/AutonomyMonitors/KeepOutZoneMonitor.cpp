/*
* KeepOutZoneMonitor.cpp
*
*  Created on: Jul 5, 2017
*      Author: Sriram and Guohui
*/

#include <iostream>
#include <memory>
#include <math.h>
#include "AutonomyMonitors/MonitorBase.h"
#include "AutonomyMonitors/KeepOutZoneMonitor.h"
#include "AutonomyMonitors/VehicleStateMessage.h"
#include "afrl/cmasi/Location3D.h"
#include "afrl/cmasi/KeepOutZone.h"
#include "afrl/cmasi/AbstractGeometry.h"
#include "afrl/cmasi/AbstractGeometryDescendants.h"
#include "UnitConversions.h"
#include "afrl/cmasi/autonomymonitor/OperatingZoneFailure.h"
#include "afrl/cmasi/autonomymonitor/OperatingZoneFailureType.h"
#include "afrl/cmasi/autonomymonitor/OperatingZoneSuccess.h"
#include "AutonomyMonitors/GeometryUtilities.h"

namespace uxas {
namespace service {
namespace monitoring {

KeepOutZoneMonitor::KeepOutZoneMonitor(AutonomyMonitorServiceMain  * service_ptr,
                                       std::shared_ptr<afrl::cmasi::KeepOutZone> keepOutZone): 
  MonitorBase(service_ptr),
  _zone(keepOutZone),
  _failed(false),
  _robustness(10000.0)
{

  // TODO: Remove these print statements if needed -- they are just for diagnostics
  if (debug) {
    std::cout << "[KeepOutZoneMonitor] Started a Keepout zone monitor" << std::endl;
    std::cout << "\t [ID]: " << keepOutZone -> getZoneID() << std::endl;
    std::cout << "\t [Altitude Range]:" << keepOutZone -> getMinAltitude() << " --> " << keepOutZone -> getMaxAltitude() << std::endl;
    std::cout << "\t [Vehicles Affected IDs]:";
    std::vector<int64_t> affectedVehicles = keepOutZone -> getAffectedAircraft();
    if (affectedVehicles.size() == 0) {
      std::cout << "All vehicles are affected" << std::endl;
    } else {
      for (auto id : affectedVehicles) {
        std::cout << id << ", ";
      }
      std::cout << std::endl;
    }
  }
  // Done unpacking
}

KeepOutZoneMonitor::~KeepOutZoneMonitor() {
  // TODO Auto-generated destructor stub
}


void KeepOutZoneMonitor::sendTaskStatus(){
  if (this -> _failed){
    auto fObj = std::make_shared<afrl::cmasi::autonomymonitor::OperatingZoneFailure>();
    fObj -> setZoneID(this -> _zone -> getZoneID());
    fObj -> setResponsibleVehicleID(fail_responsible_vehicle_id);
    fObj -> setFailureType(afrl::cmasi::autonomymonitor::OperatingZoneFailureType::KeepOutZoneFail);
    fObj -> setFailureTime(fail_timestamp);
    fObj -> setFailureLatitude(fail_latitude);
    fObj -> setFailureLongitude(fail_longitude);
    fObj -> setFailureAltitude(fail_altitude);
    fObj -> setRobustness(_robustness);
    service_ -> broadcastMessage(fObj);
  } else {
    auto fObj = std::make_shared<afrl::cmasi::autonomymonitor::OperatingZoneSuccess>();
    fObj -> setZoneID(this -> _zone -> getZoneID());
    fObj -> setRobustness(_robustness);
    service_ -> broadcastMessage(fObj);
  }

}

void KeepOutZoneMonitor::sendFailureMessage(VehicleStateMessage const & vMessage) {
  _failed = true;
  fail_latitude = vMessage.getLatitude();
  fail_longitude = vMessage.getLongitude();
  fail_altitude = vMessage.getAltitude();
  fail_responsible_vehicle_id = vMessage.getVehicleID();
  fail_timestamp = vMessage.getTimeStamp();

  auto fObj = std::make_shared<afrl::cmasi::autonomymonitor::OperatingZoneFailure>();
  fObj -> setZoneID(this -> _zone -> getZoneID());
  fObj -> setResponsibleVehicleID(vMessage.getVehicleID());
  fObj -> setFailureType(afrl::cmasi::autonomymonitor::OperatingZoneFailureType::KeepOutZoneFail);
  fObj -> setFailureTime(vMessage.getTimeStamp());
  fObj -> setFailureLatitude(vMessage.getLatitude());
  fObj -> setFailureLongitude(vMessage.getLongitude());
  fObj -> setFailureAltitude(vMessage.getAltitude());
  fObj -> setRobustness(_robustness);
  service_ -> broadcastMessage(fObj);
}

void KeepOutZoneMonitor::addVehicleStateMessage(VehicleStateMessage const & vMessage) {

  /***********************************************************************
   * Implement the checking part
   */
  // Change the longitude and latitude to be the North/East coordinates
  // using Localcoordsmodule in Utilities
  const double Latitude_deg = vMessage.getLatitude();
  const double Longitude_deg = vMessage.getLongitude();
  double currentNorth_m, currentEast_m;
  double distToViolation;

  this->flatEarth.ConvertLatLong_degToNorthEast_m(Latitude_deg, Longitude_deg, currentNorth_m, currentEast_m);
  afrl::cmasi::AbstractGeometry* zoneGeometry = this->_zone->getBoundary();

  // If the KeepOutzone is a rectangle
  auto rect = dynamic_cast<afrl::cmasi::Rectangle*>(zoneGeometry);
  if (rect) {
    const double centerLatitude_deg = rect->getCenterPoint()->getLatitude();
    const double centerLongitude_deg = rect->getCenterPoint()->getLongitude();
    double centerNorth_m = 0.0, centerEast_m = 0.0;
    this->flatEarth.ConvertLatLong_degToNorthEast_m(centerLatitude_deg, centerLongitude_deg, centerNorth_m, centerEast_m);
    // using upper left point and lower right point to characterize rectangle
    double left_East = centerEast_m - rect->getWidth() / 2;
    double upper_North = centerNorth_m + rect->getHeight() / 2;
    double right_East = centerEast_m + rect->getWidth() / 2;
    double lower_North = centerNorth_m - rect->getHeight() / 2;

    assert( left_East <= right_East);
    assert( lower_North <= upper_North);
    // check whether they belong to the rectangle

    distToViolation = std::max({ lower_North - currentNorth_m, \
                                        currentNorth_m - upper_North,        \
                                        left_East - currentEast_m,        \
                                        currentEast_m - right_East
                                      } );

    _robustness = std::min(_robustness, distToViolation);

    if ((currentNorth_m <= upper_North && currentNorth_m >= lower_North)
        && (currentEast_m <= right_East && currentEast_m >= left_East)) { // If so, warning


      std::cout << "***************************************" << std::endl;
      std::cout << "WARNING!!! YOU (vehicleID:" << vMessage.getVehicleID()
                << ") ARE IN THE DANGER ZONE: " << this->_zone->getZoneID() << "(Rectangle)" << std::endl;
      std::cout << "***************************************" << std::endl;
      std::cout << " Zone: Rectangle->" << this->_zone->getZoneID() << std::endl;
      std::cout << "   Position: " << currentNorth_m << " , " << currentEast_m << std::endl;
      std::cout << "   Center: " << centerNorth_m << ", " << centerEast_m << std::endl;
      std::cout << "   North range: " << lower_North << ", " << upper_North << std::endl;
      std::cout << "   East range: " << left_East << ", " << right_East << std::endl;

      // Make robustness negative


      sendFailureMessage(vMessage);
    }
  } // KeepOutZone is a rectangle


  auto poly = dynamic_cast<afrl::cmasi::Polygon*>(zoneGeometry);
  // If the KeepOutzone is a polygon
  if (poly) {

    // // OLD method: using a line drawn from the point to the polygon and counting the number
    // // of intersections. This is cumbersome for robustness. Slightly more expensive method
    // // can also easily calculate the robustness.

    // std::vector<afrl::cmasi::Location3D*> ptList = poly->getBoundaryPoints();
    // std::vector<std::pair<double, double>> polyBoundary;
    // for(const auto loc: ptList) {
    //   std::pair<double, double> add_temp;
    //   this->flatEarth.ConvertLatLong_degToNorthEast_m(loc->getLatitude(), loc->getLongitude(), add_temp.first, add_temp.second);
    //   polyBoundary.push_back(add_temp);
    // }
    // polyBoundary.push_back(polyBoundary[0]);
    // int nCross = 0;
    // for(int i = 0; i < polyBoundary.size()-1; i++) {
    //   // xxxx.first is the north coordinate, xxxx.second is the east coordinate
    //   std::pair<double, double> p1 = polyBoundary[i];
    //   std::pair<double, double> p2 = polyBoundary[i+1];
    //   if(p1.first == p2.first) continue;  // p1 and p2 are parallel
    //   if(currentNorth_m < p1.first && currentNorth_m < p2.first) continue;  // in extension line
    //   if(currentNorth_m >= p1.first && currentNorth_m >= p2.first) continue;  // in extension line
    //   double verticalCurrentEast = (currentNorth_m - p1.first) * (p2.second - p1.second) / (p2.first - p1.first) + p1.second;
    //   if(verticalCurrentEast > currentEast_m) nCross++; // one-side intersection
    // }
    // if(nCross % 2 == 1) {
    //   std::cout << "***************************************" << std::endl;
    //   std::cout << "WARNING!!! YOU(vehicleID:" << vMessage.getVehicleID()
    //             << ") ARE IN THE DANGER ZONE: " <<this->_zone->getZoneID() << "(Polygon)" << std::endl;
    //   std::cout << "***************************************" << std::endl;
    //   sendFailureMessage(vMessage);
    // }

    auto const & cFoot = vMessage.getCameraFootprint();
    std::vector< std::pair<double, double> > polygonCoordinates;

    for (auto loc : cFoot) {
      auto xy_loc = get_east_north_coordinates(this-> flatEarth, loc.get());
      polygonCoordinates.push_back(xy_loc);
    }

    MonitorPolygon footPrint (polygonCoordinates);
    bool insidePoly;
    double robustness;
    std::tie(insidePoly, distToViolation) = footPrint.isMember(currentEast_m, currentNorth_m);
    _robustness = std::min(_robustness, -1.0 * distToViolation);
    if (insidePoly) {
      std::cout << "***************************************" << std::endl;
      std::cout << "WARNING!!! YOU(vehicleID:" << vMessage.getVehicleID()
                << ") IS IN THE DANGER ZONE: " << this->_zone->getZoneID() << "(Polygon)" << std::endl;
      std::cout << "***************************************" << std::endl;
      sendFailureMessage(vMessage);
    }
  }

  // If the KeepOutzone is a circle
  auto circle = dynamic_cast<afrl::cmasi::Circle*>(zoneGeometry);
  if (circle) {
    double circle_radius = circle->getRadius();
    double circle_center_North_m, circle_center_East_m;
    flatEarth.ConvertLatLong_degToNorthEast_m(circle->getCenterPoint()->getLatitude(), 
                                              circle->getCenterPoint()->getLongitude(), 
                                              circle_center_North_m, 
                                              circle_center_East_m);
    double dist_to_center = sqrt( (currentEast_m - circle_center_East_m) * (currentEast_m - circle_center_East_m) + 
                                  (currentNorth_m - circle_center_North_m) * (currentNorth_m - circle_center_North_m) );
    _robustness = std::min(_robustness, dist_to_center - circle_radius);
    if (dist_to_center < circle_radius)
    {
      std::cout << "***************************************" << std::endl;
      std::cout << "WARNING!!! YOU(vehicleID:" << vMessage.getVehicleID() << ") ARE IN THE DANGER ZONE: " 
                << this->_zone->getZoneID() << "(Circle)" << std::endl;
      std::cout << "***************************************" << std::endl;
      sendFailureMessage(vMessage);
    }
  }

  return;
}

bool KeepOutZoneMonitor::isPropertySatisfied() {
  // don't touch it yet. Just put all things in the addvehiclestatemessage()
  std::cout << "testFor: ispropertysatisfied()" << std::endl;
  return (!this -> _failed);
}

double KeepOutZoneMonitor::propertyRobustness() {
  std::cout << "testFor: propertyrobustness()" << std::endl;
  return _robustness;
}

} /* namespace monitoring */
} /* namespace service */
} /* namespace uxas */
