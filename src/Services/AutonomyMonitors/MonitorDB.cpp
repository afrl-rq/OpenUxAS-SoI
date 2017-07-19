
#include <iostream>
#include <map>
#include <vector>
#include <memory>

#include "afrl/cmasi/AirVehicleState.h"
#include "afrl/cmasi/AirVehicleConfiguration.h"
#include "uxas/messages/task/UniqueAutomationRequest.h"
#include "uxas/messages/task/UniqueAutomationResponse.h"
#include "afrl/cmasi/EntityState.h"
#include "afrl/cmasi/KeepInZone.h"
#include "afrl/cmasi/KeepOutZone.h"
#include "afrl/cmasi/Task.h"
#include "afrl/cmasi/TaskDescendants.h"

#include "afrl/impact/PointOfInterest.h"
#include "afrl/impact/LineOfInterest.h"
#include "afrl/impact/AreaOfInterest.h"

#include "AutonomyMonitors/MonitorDB.h"
#include "AutonomyMonitors/MonitorUtils.h"
#include "AutonomyMonitors/MonitorBase.h"
#include "AutonomyMonitors/VehicleStateMessage.h"
#include "AutonomyMonitors/KeepOutZoneMonitor.h"
#include "AutonomyMonitors/KeepInZoneMonitor.h"

namespace uxas {
  namespace service {
    namespace monitoring {

      MonitorDB::MonitorDB() {};
      MonitorDB::~MonitorDB() {};
      void MonitorDB::addMonitor(MonitorBase* what)
        {
          allMonitors.push_back(what);
          return;
        }

      void MonitorDB::registerVehicleState(VehicleStateMessage  vMessage){
        allVehicleStateMessages.push_back(vMessage);
        for (MonitorBase* mon: allMonitors){
          mon -> addVehicleStateMessage(vMessage);
        }
      }

      bool MonitorDB::processEntityState(std::shared_ptr<afrl::cmasi::EntityState> ptr){
          VehicleStateMessage vMessage(ptr);
          registerVehicleState(vMessage);
          return true;
      }

      bool MonitorDB::processEntityConfiguration(std::shared_ptr<afrl::cmasi::EntityConfiguration> ptr) {
        return true; //Do nothing for the time being, we will implement this later
      }

      bool MonitorDB::processUniqueAutomationRequest(std::shared_ptr<uxas::messages::task::UniqueAutomationRequest> ptr){
        return true; // Do nothing for the time being, we will implement this later
      }

      bool MonitorDB::processUniqueAutomationResponse(std::shared_ptr<uxas::messages::task::UniqueAutomationResponse> ptr){
        return true; // Do nothing for the time being, we will implement this later
      }

      bool MonitorDB::processOperatingRegion(std::shared_ptr<afrl::cmasi::OperatingRegion> ptr){
        return true;
      }
      bool MonitorDB::processKeepInZone(std::shared_ptr<afrl::cmasi::KeepInZone> ptr){
        KeepInZoneMonitor * kizm  = new KeepInZoneMonitor(ptr);
        this->addMonitor(kizm);
        return true;
      }
      bool MonitorDB::processKeepOutZone(std::shared_ptr<afrl::cmasi::KeepOutZone> ptr){
        KeepOutZoneMonitor * kozm = new KeepOutZoneMonitor(ptr);
        this -> addMonitor(kozm);
        return true;
      }
      bool MonitorDB::processAreaOfInterest(std::shared_ptr<afrl::impact::AreaOfInterest> ptr){
        return true;
      }
      bool MonitorDB::processLineOfInterest(std::shared_ptr<afrl::impact::LineOfInterest> ptr){
        return true;
      }
      bool MonitorDB::processPointOfInterest(std::shared_ptr<afrl::impact::PointOfInterest> ptr){
        return true;
      }
      bool MonitorDB::processTask(std::shared_ptr<afrl::cmasi::Task> ptr){
        return true;
      }


    };
  };
};
