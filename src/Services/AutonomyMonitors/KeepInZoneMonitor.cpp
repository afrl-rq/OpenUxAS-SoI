/*
 * KeepInZonemonitor.cpp
 *
 * Created on 7/11/17
 * Author: Srirm and Guohui
 *
 */

#include <iostream>
#include <memory>
#include "math.h"
#include "afrl/cmasi/autonomymonitor/OperatingZoneSuccess.h"
#include "AutonomyMonitors/KeepInZoneMonitor.h"
#include "AutonomyMonitors/MonitorBase.h"
#include "AutonomyMonitors/GeometryUtilities.h"
#include "afrl/cmasi/autonomymonitor/OperatingZoneMonitorStarted.h"
#include "afrl/cmasi/autonomymonitor/OperatingZoneFailureType.h"


namespace uxas {
namespace service {
namespace monitoring {

KeepInZoneMonitor::KeepInZoneMonitor(AutonomyMonitorServiceMain * service_ptr,
                                     std::shared_ptr<afrl::cmasi::KeepInZone> keepInZone): MonitorBase(service_ptr),
  _zone(keepInZone),
  _failed(false),
  _robustness(0.0) {
  sendMonitorStartMessage();
  if (debug) {
    //TODO: Remove the print statements if necessary -- they are used for diagnostics
    std::cout << "[KeepInZoneMonitor] Started a Keepin zone monitor" << std::endl;
    std::cout << "\t [ID]: " << keepInZone->getZoneID() << std::endl;
    std::cout << "\t [Altitude Range: ]" << keepInZone->getMinAltitude() << "-->" << keepInZone->getMaxAltitude() << std::endl;
    std::cout << "\t [Vehicle Affected IDs]: ";
    std::vector<int64_t> affectedVehicles = keepInZone->getAffectedAircraft();
    if (affectedVehicles.size() == 0) {
      std::cout << "All vehicles are affected" << std::endl;
    } else {
      for (auto id : affectedVehicles) {
        std::cout << id << ", ";
      }
      std::cout << std::endl;
    }
    // Done unpacking
  }
}

void KeepInZoneMonitor::sendMonitorStartMessage() {
  auto fObj = std::make_shared<afrl::cmasi::autonomymonitor::OperatingZoneMonitorStarted>();
  fObj -> setZoneID(this -> _zone -> getZoneID());
  fObj -> setZoneType(afrl::cmasi::autonomymonitor::OperatingZoneFailureType::KeepInZoneFail);
  service_ -> broadcastMessage(fObj);
}


KeepInZoneMonitor::~KeepInZoneMonitor() {}

void KeepInZoneMonitor::sendTaskStatus() {
  if (this -> _failed) {
    auto fObj = std::make_shared<afrl::cmasi::autonomymonitor::OperatingZoneFailure>();
    fObj -> setZoneID(this -> _zone -> getZoneID());
    fObj -> setResponsibleVehicleID(fail_responsible_vehicle_id);
    fObj -> setFailureType(afrl::cmasi::autonomymonitor::OperatingZoneFailureType::KeepInZoneFail);
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

void KeepInZoneMonitor::sendFailureMessage(VehicleStateMessage const & vMessage) {
  fail_latitude = vMessage.getLatitude();
  fail_longitude = vMessage.getLongitude();
  fail_responsible_vehicle_id = vMessage.getTimeStamp();
  fail_timestamp = vMessage.getTimeStamp();
  fail_altitude = vMessage.getAltitude();

  auto fObj = std::make_shared<afrl::cmasi::autonomymonitor::OperatingZoneFailure>();
  fObj -> setZoneID(this -> _zone -> getZoneID());
  fObj -> setResponsibleVehicleID(fail_responsible_vehicle_id);
  fObj -> setFailureType(afrl::cmasi::autonomymonitor::OperatingZoneFailureType::KeepInZoneFail);
  fObj -> setFailureTime(fail_timestamp);
  fObj -> setFailureLatitude(fail_latitude);
  fObj -> setFailureLongitude(fail_longitude);
  fObj -> setFailureAltitude(fail_altitude);
  fObj -> setRobustness(_robustness);
  this -> _failed = true;
  service_ -> broadcastMessage(fObj);
}

void KeepInZoneMonitor::addVehicleStateMessage(VehicleStateMessage const & vMessage)
{

  const double Latitude_deg = vMessage.getLatitude();
  const double Longitude_deg = vMessage.getLongitude();
  double currentNorth_m, currentEast_m;
  double distToViolation;
  flatEarth.ConvertLatLong_degToNorthEast_m(Latitude_deg, Longitude_deg, currentNorth_m, currentEast_m);
  afrl::cmasi::AbstractGeometry* zoneGeometry = this->_zone->getBoundary();
  // If the KeepInZone is a rectangle
  auto rect = dynamic_cast<afrl::cmasi::Rectangle*>(zoneGeometry);
  if (rect) {
    const double centerLatitude_deg = rect->getCenterPoint()->getLatitude();
    const double centerLongitude_deg = rect->getCenterPoint()->getLongitude();
    double centerNorth_m, centerEast_m;
    flatEarth.ConvertLatLong_degToNorthEast_m(centerLatitude_deg, centerLongitude_deg, centerNorth_m, centerEast_m);
    double upperleft_East = centerEast_m - rect->getWidth() / 2.0;
    double upperleft_North = centerNorth_m + rect->getHeight() / 2.0;
    double lowerright_East = centerEast_m + rect->getWidth() / 2.0;
    double lowerright_North = centerNorth_m - rect->getHeight() / 2.0;
    distToViolation = std::min({ currentNorth_m - lowerright_North,   \
                                 upperleft_North - currentNorth_m,   \
                                 currentEast_m - upperleft_East,      \
                                 lowerright_East - currentEast_m      \
                               });
    _robustness = std::min(_robustness, distToViolation);
    // KeepInZone conditions
    if ((currentNorth_m <= upperleft_North && currentNorth_m >= lowerright_North) && \
        (currentEast_m <= lowerright_East && currentEast_m >= upperleft_East)) {
      if (debug) {
        std::cout << " Zone: Rectangle->" << this->_zone->getZoneID() << std::endl;
        std::cout << "   Center: " << centerNorth_m << ", " << centerEast_m << std::endl;
        std::cout << "   upperleft: " << upperleft_North << ", " << upperleft_East << std::endl;
        std::cout << "   lowerright: " << lowerright_North << ", " << lowerright_East << std::endl;
      }
    } else {
      std::cout << "***************************************" << std::endl;
      std::cout << "WARNING!!! YOU(vehilceID: )" << vMessage.getVehicleID()
                << ") ARE OUT OF THE ZONE: " << this->_zone->getZoneID() << "Rectangle" << std::endl;
      std::cout << "***************************************" << std::endl;
      sendFailureMessage(vMessage);
    }
  }

  // If the KeepInZone is a polygon
  auto poly = dynamic_cast<afrl::cmasi::Polygon*>(zoneGeometry);
  if (poly) {
    /**
        std::vector<afrl::cmasi::Location3D*> ptList = poly->getBoundaryPoints();
        std::vector<std::pair<double, double>> polyBoundary;
        for (const auto loc : ptList) {
          std::pair<double, double> add_temp;
          flatEarth.ConvertLatLong_degToNorthEast_m(loc->getLatitude(), loc->getLongitude(), add_temp.first, add_temp.second);
          polyBoundary.push_back(add_temp);
        }
        polyBoundary.push_back(polyBoundary[0]);
        int nCross = 0;
        for (int i = 0; i < polyBoundary.size() - 1; i++) { // count the number of one-side intersections
          std::pair<double, double> p1 = polyBoundary[i];
          std::pair<double, double> p2 = polyBoundary[i + 1];
          if (p1.first == p2.first) continue; // p1 and p2 are parallel
          if (currentNorth_m < p1.first && currentNorth_m < p2.first) continue; // in extension line
          if (currentNorth_m >= p1.first && currentNorth_m >= p2.first) continue; // in extension line
          double verticalCurrentEast = (currentNorth_m - p1.first) * (p2.second - p1.second) / (p2.first - p1.first) + p1.second;
          if (verticalCurrentEast > currentEast_m) nCross++;
        }
        if (nCross % 2) { // vehicle is in the KeepInZone
          if (debug) {
            std::cout << " Zone: Polygon->" << this->_zone->getZoneID() << std::endl;
            std::cout << " Boundaries: " << std::endl;
            for (auto loc : polyBoundary) {
              std::cout << " " << loc.first << ", " << loc.second << " ->";
            }
            std::cout << std::endl;
          }
        } else {
          std::cout << "***************************************" << std::endl;
          std::cout << "WARNING!!! YOU (vehicleID:" << vMessage.getVehicleID()
                    << ") ARE OUT OF THE ZONE: " << this->_zone->getZoneID() << "(Polygon)" << std::endl;
          std::cout << "***************************************" << std::endl;
          sendFailureMessage(vMessage);
        }
    **/
    // Copy and paste from KeepInZoneMonitor
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
    _robustness = std::min(_robustness, distToViolation);
    if (!insidePoly) {
      std::cout << "***************************************" << std::endl;
      std::cout << "WARNING!!! YOU(vehicleID:" << vMessage.getVehicleID()
                << ") IS OUTSIDE the KEEPINZONE: " << this->_zone->getZoneID() << "(Polygon)" << std::endl;
      std::cout << "***************************************" << std::endl;
      sendFailureMessage(vMessage);
    }

  }

  // If the KeepInZone is a circle
  auto circle = dynamic_cast<afrl::cmasi::Circle*>(zoneGeometry);
  if (circle) {
    double circle_radius = circle->getRadius();
    double circle_center_North_m, circle_center_East_m;
    flatEarth.ConvertLatLong_degToNorthEast_m(circle->getCenterPoint()->getLatitude(),
        circle->getCenterPoint()->getLongitude(),
        circle_center_North_m,
        circle_center_East_m);
    double distance_from_center = sqrt((currentEast_m - circle_center_East_m) * (currentEast_m - circle_center_East_m) +
                                       (currentNorth_m - circle_center_North_m) * (currentNorth_m - circle_center_North_m));
    _robustness = std::min(_robustness, circle_radius - distance_from_center);

    if (distance_from_center < circle_radius) {
      if (debug) {
        std::cout << " Zone: " << this->_zone->getZoneID() << std::endl;
        std::cout << "  Center: " << circle->getCenterPoint()->getLatitude() << ", " << circle->getCenterPoint()->getLongitude() << std::endl;
        //std::cout << " Center: " << circle_center_North_m << ", " << circle_center_East_m << std::endl;
        std::cout << "  Radius: " << circle_radius << std::endl;
      }
    } else {
      std::cout << "***************************************" << std::endl;
      std::cout << "WARNING!!! YOU (vehilceID: " << vMessage.getVehicleID()
                << ") ARE OUT OF THE ZONE: " << this->_zone->getZoneID() << "(Cirlce)" << std::endl;
      std::cout << "***************************************" << std::endl;
      sendFailureMessage(vMessage);
    }
  }

  return;
}

bool KeepInZoneMonitor::isPropertySatisfied()
{
  return (! _failed);
}

double KeepInZoneMonitor::propertyRobustness()
{
  return 0.0;
}



}
}
}
