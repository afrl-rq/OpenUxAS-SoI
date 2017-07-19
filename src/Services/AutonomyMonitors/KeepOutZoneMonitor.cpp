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
#include "../../Utilities/UnitConversions.h"

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
        std::cout << "[Vehicle: " << vMessage.getVehicleID() << "]"
                  << " in [KeepOutZone: " << this->_zone->getZoneID() << "]" << std::endl;
        /*
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
        */
        /***********************************************************************
         * Implement the checking part
         */
        // Change the longitude and latitude to be the North/East coordinates
        // using Localcoordsmodule in Utilities
        const double Latitude_deg = vMessage.getLatitude();
        const double Longitude_deg = vMessage.getLongitude();
        double currentNorth_m, currentEast_m;
        /*
         * I'm using the class in ../Utilities/UnitConversions.h to change Lat/Lon
         * to the North/East coordinates and check. I put the flatEarth in the
         * header file.
         *
         * It's a litte different with the example, because I can't initialize
         * the origin of the North/East cordinates locally or in the constructor,
         * but it doesn't affect the calculation. And I find out that the function
         * ConvertLatLong_degToNorthEast_m() will be initialized by the first
         * Keepxxxx.xml file called by AssignTasks_cfg.xml. (e.g., now the
         * KeepOutZone_1 (it is a rectangle) is the first zone message called in AssignTasks_cfg.xml,
         * the ConvertLatLong_degToNorthEast_m() will be initialized by the center
         * of rectangle. If we put KeepInZone_3 before KeepOutZone_2, ConvertLatLong_degToNorthEast_m() will be initialized by the first point of polygon
         * in KeepInZone_3) It's just the difference of the origin choices, I checked
         * the performance and it doesn't affect the results.
         *
         */
        //std::shared_ptr<uxas::common::utilities::CUnitConversions> flatEarth(new uxas::common::utilities::CUnitConversions());
        //flatEarth->Initialize(Latitude_deg, Longitude_deg);
        this->flatEarth->ConvertLatLong_degToNorthEast_m(Latitude_deg, Longitude_deg, currentNorth_m, currentEast_m);
        std::cout << "\t [[Current_Position: ]]" << currentNorth_m << ", "
                  << currentEast_m << std::endl;

        // Define the possible KeepOutZone types
        afrl::cmasi::AbstractGeometry* zoneGeometry = this->_zone->getBoundary();
        // If the KeepOutzone is a rectangle
        auto rect = dynamic_cast<afrl::cmasi::Rectangle*>(zoneGeometry);
        if(rect) {
          const double centerLatitude_deg = rect->getCenterPoint()->getLatitude();
          const double centerLongitude_deg = rect->getCenterPoint()->getLongitude();
          double centerNorth_m, centerEast_m; 
          this->flatEarth->ConvertLatLong_degToNorthEast_m(centerLatitude_deg, centerLongitude_deg, centerNorth_m, centerEast_m);
          // using upper left point and lower right point to characterize rectangle
          double upperleft_East = centerEast_m - rect->getWidth()/2;
          double upperleft_North = centerNorth_m + rect->getHeight()/2;
          double lowerright_East = centerEast_m + rect->getWidth()/2;
          double lowerright_North = centerNorth_m - rect->getHeight()/2;
          // check whether they belong to the rectangle
          if((currentNorth_m <= upperleft_North && currentNorth_m >= lowerright_North) && (currentEast_m <= lowerright_East && currentEast_m >= upperleft_East)) { // If so, warning
            std::cout << "***************************************" << std::endl;
            std::cout << "WARNING!!! YOU (vehicleID:" << vMessage.getVehicleID()
                      << ") ARE IN THE DANGER ZONE: " <<this->_zone->getZoneID() << "(Rectangle)"<< std::endl;
            std::cout << "***************************************" << std::endl;
          }
          else { // otherwise, show info
            std::cout << " Zone: Rectangle->" << this->_zone->getZoneID() << std::endl;
            std::cout << "   Center: " << centerNorth_m << ", " << centerEast_m << std::endl;
            std::cout << "   upperleft: " << upperleft_North << ", " << upperleft_East<< std::endl;
            std::cout << "   lowerright: " << lowerright_North << ", " << lowerright_East << std::endl;
            //std::cout << "    Width: " << rect->getWidth() << " Height: " << rect->getHeight() << std::endl;
          }
        }
        
        // If the KeepOutzone is a polygon
        auto poly = dynamic_cast<afrl::cmasi::Polygon*>(zoneGeometry);
        if(poly) {
          std::vector<afrl::cmasi::Location3D*> ptList = poly->getBoundaryPoints();
          std::vector<std::pair<double, double>> polyBoundary;
          for(const auto loc: ptList) {
            std::pair<double, double> add_temp;
            this->flatEarth->ConvertLatLong_degToNorthEast_m(loc->getLatitude(), loc->getLongitude(), add_temp.first, add_temp.second);
            polyBoundary.push_back(add_temp);
          }
          polyBoundary.push_back(polyBoundary[0]);
          int nCross = 0;
          for(int i = 0; i < polyBoundary.size()-1; i++) {
            // xxxx.first is the north coordinate, xxxx.second is the east coordinate
            std::pair<double, double> p1 = polyBoundary[i];
            std::pair<double, double> p2 = polyBoundary[i+1];
            if(p1.first == p2.first) continue;  // p1 and p2 are parallel
            if(currentNorth_m < p1.first && currentNorth_m < p2.first) continue;  // in extension line
            if(currentNorth_m >= p1.first && currentNorth_m >= p2.first) continue;  // in extension line
            double verticalCurrentEast = (currentNorth_m - p1.first) * (p2.second - p1.second) / (p2.first - p1.first) + p1.second;
            if(verticalCurrentEast > currentEast_m) nCross++; // one-side intersection
          }
          if(nCross % 2 == 1) {
            std::cout << "***************************************" << std::endl;
            std::cout << "WARNING!!! YOU(vehicleID:" << vMessage.getVehicleID()
                      << ") ARE IN THE DANGER ZONE: " <<this->_zone->getZoneID() << "(Polygon)" << std::endl;
            std::cout << "***************************************" << std::endl;
          }
          else {
            std::cout << " Zone: Polygon->" << this->_zone->getZoneID() << std::endl;
            std::cout << " Boundaries: " << std::endl;
            for(auto loc: polyBoundary) {
              std::cout << " " << loc.first << ", " << loc.second << std::endl;
            }
          }
        }
        
        // If the KeepOutzone is a circle
        auto circle = dynamic_cast<afrl::cmasi::Circle*>(zoneGeometry);
        if(circle) {
          double circle_radius = circle->getRadius();
          double circle_center_North_m, circle_center_East_m;
          flatEarth->ConvertLatLong_degToNorthEast_m(circle->getCenterPoint()->getLatitude(), circle->getCenterPoint()->getLongitude(), circle_center_North_m, circle_center_East_m);
          if(sqrt((currentEast_m - circle_center_East_m) * (currentEast_m - circle_center_East_m) + (currentNorth_m - circle_center_North_m) * (currentNorth_m - circle_center_North_m)) < circle_radius) {
            std::cout << "***************************************" << std::endl;
            std::cout << "WARNING!!! YOU(vehicleID:" << vMessage.getVehicleID() << ") ARE IN THE DANGER ZONE: " <<this->_zone->getZoneID() << "(Circle)" << std::endl;
            std::cout << "***************************************" << std::endl;
          } else {
            std::cout << " Zone: Cicle-> " << this->_zone->getZoneID() << std::endl;
            std::cout << "  CenterPosition: " << circle->getCenterPoint()->getLatitude() << ", " << circle->getCenterPoint()->getLongitude() << std::endl;
            std::cout << "  Radius: " << circle_radius << std::endl;
          }  
        }

        return;
      }

      bool KeepOutZoneMonitor::isPropertySatisfied(){
        // don't touch it yet. Just put all things in the addvehiclestatemessage()
        std::cout << "testFor: ispropertysatisfied()" << std::endl;
        return true;
      }
      double KeepOutZoneMonitor::propertyRobustness(){
        std::cout << "testFor: propertyrobustness()" <<std::endl;
        return 0.0;
      }

    } /* namespace monitoring */
  } /* namespace service */
} /* namespace uxas */
