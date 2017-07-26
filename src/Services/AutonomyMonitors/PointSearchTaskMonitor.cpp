#include "iostream"

#include "AutonomyMonitors/PointSearchTaskMonitor.h"
#include "UnitConversions.h"
#include "afrl/cmasi/autonomymonitor/TaskFailure.h"
#include "afrl/cmasi/autonomymonitor/TaskSuccess.h"
#include "afrl/cmasi/autonomymonitor/TaskMonitorStarted.h"

namespace uxas {
namespace service {
namespace monitoring {
  
  PointSearchTaskMonitor::PointSearchTaskMonitor(AutonomyMonitorServiceMain * service_ptr, std::shared_ptr<afrl::cmasi::PointSearchTask> pointSearchTask):MonitorBase(service_ptr), _task(pointSearchTask), _failed(true) {
    //this->debug = true; // Debug 
    sendMonitorStartMessage();
    if(debug){
      std::cout << "[PointSearchTask] Start searching" << std::endl;
      std::cout << "\t [ID]: " << _task->getTaskID() << std::endl;
      std::cout << "\t [Search Location]: " << this->_task->getSearchLocation()->getLatitude()
                << ", " << this->_task->getSearchLocation()->getLongitude() << std::endl;
      std::cout << "\t [Standoffdistance]: " << this->_task->getStandoffDistance() << std::endl;
      //auto viewAngleList = this->_task->getViewAngleList();
      std::vector<afrl::cmasi::Wedge*> viewAngleList = this->_task->getViewAngleList();
      std::cout << "Viewanglelist: " << std::endl;
      for(auto item: viewAngleList) {
        std::cout <<"\t" << item->getAzimuthCenterline() << ", " << item->getAzimuthExtent() << "|"
                  << item->getVerticalCenterline() << ", " << item->getVerticalExtent()<< std::endl;
      }
    }
  };

  PointSearchTaskMonitor::~PointSearchTaskMonitor(){}; // Destructor

  void PointSearchTaskMonitor::addVehicleStateMessage(VehicleStateMessage const & vMessage){
    // Change the current longitude and latitude to be the North/East coordinates
    // using Localcoordsmodule in Utilities
    const double Latitude_deg = vMessage.getLatitude();
    const double Longitude_deg = vMessage.getLongitude();
    double currentNorth_m, currentEast_m;
    std::shared_ptr<uxas::common::utilities::CUnitConversions> flatEarth(new uxas::common::utilities::CUnitConversions());
    flatEarth->ConvertLatLong_degToNorthEast_m(Latitude_deg, Longitude_deg, currentNorth_m, currentEast_m);
    // Get the camerafootprint of the vehicle and transfer them to be North/East coordinates
    // The incoming footprints should be ordered clockwise or counterclockwise.
    //std::vector<afrl::cmasi::Location3D*> footprint_latlong = vMessage.getCameraFootprint();
    std::vector<std::shared_ptr<afrl::cmasi::Location3D>> footprint_latlong = vMessage.getCameraFootprint();
    std::vector<std::pair<double, double>> footprint_m;
    for(auto loc: footprint_latlong) {
      std::pair<double, double> fp_add;
      flatEarth->ConvertLatLong_degToNorthEast_m(loc->getLatitude(), loc->getLongitude(), fp_add.first, fp_add.second);
      footprint_m.push_back(fp_add);
    }
    footprint_m.push_back(footprint_m[0]);
    // The footprints will constitue a polygon, the algorithm should check whether
    // the target point is in the polygon constituted by the footprints
    double target_North_m, target_East_m;
    flatEarth->ConvertLatLong_degToNorthEast_m(this->_task->getSearchLocation()->getLatitude(), this->_task->getSearchLocation()->getLongitude(), target_North_m, target_East_m);
    int nCross = 0;
    for(int i = 0; i < footprint_m.size()-1; i++) {
      // xxx.first is the north coordinate, xxx.second is the east coordinate
      std::pair<double, double> p1 = footprint_m[i];
      std::pair<double, double> p2 = footprint_m[i+1];
      if(p1.first == p2.first) continue; // p1 and p2 are parallel
      if(target_North_m < p1.first && target_North_m < p2.first) continue; // in extension line
      if(target_North_m >= p1.first && target_North_m >= p2.first) continue; // in extension line
      double verticalCurrentEast = (target_North_m - p1.first) * (p2.second - p1.second) / (p2.first - p1.first) + p1.second;
      if(verticalCurrentEast > target_East_m) nCross++;
    }
    if(nCross % 2 == 1) {
      std::cout << "*********************************************" << std::endl;
      std::cout << "Congratulations!!! [VehilceID " << vMessage.getVehicleID()
                << "] --->> the target: (" << this->_task->getSearchLocation()->getLatitude()
                << ", "<< this->_task->getSearchLocation()->getLongitude() << ")"<< std::endl;
      std::cout << "\t\t   [VehicleID " << vMessage.getVehicleID() << "] Position: ("
                << Latitude_deg << ", " << Longitude_deg << ")" << std::endl;
      std::cout << "*********************************************" << std::endl;
      // Because we don't have sendfailuremessage() to show the fail messages,
      // The mission will not fail when touch the target
      this->_failed = false;
    }
    // Debug information
    if(debug) {
      std::cout << "[Vehicle: " << vMessage.getVehicleID() << "]" << " Current position (deg): "
                << vMessage.getLatitude() << ", " << vMessage.getLongitude() << std::endl;
      std::cout << "\t    " << " Current position (m): " << currentNorth_m << ", " << currentEast_m << std::endl;
      std::cout << " TargetID: " << this->_task->getTaskID() << "-> Position: (deg): "
                << this->_task->getSearchLocation()->getLatitude() << ", "
                << this->_task->getSearchLocation()->getLongitude() << std::endl;
      std::cout << "\t      " << " Position (m): " << target_North_m << ", " << target_East_m << std::endl;
      std::cout << "  Footprints: " << std::endl;
      for(auto item: footprint_m) {
        std::cout << "  " << item.first << ", " << item.second << std::endl;
      }
    }
    
  }


  void PointSearchTaskMonitor::sendMonitorStartMessage(){
    auto fObj = std::make_shared<afrl::cmasi::autonomymonitor::TaskMonitorStarted>();
    fObj -> setTaskID( this -> _task -> getTaskID());
    service_ -> broadcastMessage(fObj);
  }

  bool PointSearchTaskMonitor::isPropertySatisfied(){
    return !this->_failed;
  }

  double PointSearchTaskMonitor::propertyRobustness(){
    return 0.0;
  }

  void PointSearchTaskMonitor::sendTaskStatus(){
    if(this->isPropertySatisfied()) {
      std::cout << "[PointSearchTaskMonitor]: SUCESS!!!" << std::endl;
      auto fObj = std::make_shared<afrl::cmasi::autonomymonitor::TaskSuccess>();
      fObj->setTaskID(this->_task->getTaskID());
      service_->broadcastMessage(fObj);
    } else {
      std::cout << "[PointSearchTaskMonitor]: FAILURE!!!" << std::endl;
      auto fObj = std::make_shared<afrl::cmasi::autonomymonitor::TaskFailure>();
      fObj->setTaskID(this->_task->getTaskID());
      service_->broadcastMessage(fObj);
    }
  }
  
}
}
}
