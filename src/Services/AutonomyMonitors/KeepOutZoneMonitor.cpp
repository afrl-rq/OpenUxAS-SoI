/*
* KeepOutZoneMonitor.cpp
*
*  Created on: Jul 5, 2017
*      Author: Sriram and Guohui
*/

#include <iostream>
#include <memory>

#include "AutonomyMonitors/MonitorBase.h"
#include "AutonomyMonitors/KeepOutZoneMonitor.h"
#include "AutonomyMonitors/VehicleStateMessage.h"
#include "afrl/cmasi/Location3D.h"
#include "afrl/cmasi/KeepOutZone.h"
#include "afrl/cmasi/AbstractGeometry.h"
#include "afrl/cmasi/AbstractGeometryDescendants.h"

namespace uxas {
  namespace service {
    namespace monitoring {
      KeepOutZoneMonitor::KeepOutZoneMonitor(std::shared_ptr<afrl::cmasi::KeepOutZone> keepOutZone): _zone(keepOutZone) {
        // TODO: Remove these print statements if needed -- they are just for diagnostics
        std::cout << "[KeepOutZoneMonitor] Started a Keepout zone monitor" << std::endl;
        std::cout << "\t [ID]: " << keepOutZone -> getZoneID() << std::endl;
        std::cout << "\t [Altitude Range]:" << keepOutZone -> getMinAltitude() << " --> " << keepOutZone -> getMaxAltitude() << std::endl;
        std::cout << "\t [Vehicles Affected IDs]:";
        std::vector<int64_t> affectedVehicles = keepOutZone -> getAffectedAircraft();
        if (affectedVehicles.size() == 0){
            std::cout << "All vehicles are affected" << std::endl;
        } else {
          for (auto id: affectedVehicles){
            std::cout << id << ", ";
          }
          std::cout << std::endl;
        }
        // We can ignore start and end timeStamp
        afrl::cmasi::AbstractGeometry* zoneGeometry = keepOutZone -> getBoundary();
        // Is it a circle?
        auto circle = dynamic_cast<afrl::cmasi::Circle*>(zoneGeometry);
        if (circle){
          std::cout << "\t [Circle:] C (" << circle -> getCenterPoint() -> getLatitude()
            << "," << circle -> getCenterPoint() -> getLongitude()
            << ") R: " << circle -> getRadius() << std::endl;
        }

        // Is it a rectangle?
        auto rect = dynamic_cast<afrl::cmasi::Rectangle*>(zoneGeometry);
        if (rect){
          std::cout << "\t [Rectangle:] Center(" << rect -> getCenterPoint() -> getLatitude() << " , "
            << rect -> getCenterPoint() -> getLongitude() << "), W:" << rect -> getWidth() << " (meters?) H:" <<
            rect -> getHeight() << " (meters?) " << std::endl;
        }

        // Is it a polygon?
        auto poly = dynamic_cast<afrl::cmasi::Polygon*>(zoneGeometry);
        if (poly){
          std::cout << "\t [Polygon] List of points (lat, long)" << std::endl;
          std::vector<afrl::cmasi::Location3D*> ptList = poly -> getBoundaryPoints();
          for (const auto loc: ptList){
              std::cout << "\t\t" << loc -> getLatitude() << ", " << loc -> getLongitude() << std::endl;
          }
        }
        // Done unpacking
      }

      KeepOutZoneMonitor::~KeepOutZoneMonitor() {
        // TODO Auto-generated destructor stub
      }

      void KeepOutZoneMonitor::addVehicleStateMessage(VehicleStateMessage const & vMessage){
        // TODO: Take this message away and implement the actual logic
        std::cout << "[KeepOutZoneMonitor] Got vehicle state message:" << std::endl;
        std::cout << "\t [VehicleID] " << vMessage.getVehicleID() << std::endl;
        std::cout << "\t [TimeStamp] " << vMessage.getTimeStamp() << std::endl;
        std::cout << "\t [Latitude] " << vMessage.getLatitude() << std::endl;
        std::cout << "\t [Longitude] " << vMessage.getLongitude() << std::endl;
        std::cout << "\t [Altitude] " << vMessage.getAltitude() << std::endl;
        std::cout << "\t [CameraFootprint] " << std::endl;
        std::vector<afrl::cmasi::Location3D*> const & footprint = vMessage.getCameraFootprint();
        for(const auto loc: footprint){
          std::cout << "\t\t" << loc -> getLatitude() << ", " << loc -> getLongitude() << std::endl;
        }
        return;
      }

      bool KeepOutZoneMonitor::isPropertySatisfied(){
        return true;
      }
      double KeepOutZoneMonitor::propertyRobustness(){
        return 0.0;
      }

    } /* namespace monitoring */
  } /* namespace service */
} /* namespace uxas */
