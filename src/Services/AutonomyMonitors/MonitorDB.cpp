
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
#include "AutonomyMonitors/PointSearchTaskMonitor.h"
#include "AutonomyMonitors/LineSearchTaskMonitor.h"
#include "AutonomyMonitors/AreaSearchTaskMonitor.h"


namespace uxas {
  namespace service {
    namespace monitoring {

      MonitorDB::MonitorDB(AutonomyMonitorServiceMain  * service_ptr): service_(service_ptr) {};
      MonitorDB::~MonitorDB() {
	for (auto m: allMonitors){
	  delete(m);
	}
      }
      
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
	// Start a monitor for all keep in zones
	for (auto id: ptr -> getKeepInAreas()){
	  auto it = keepInZones.find(id);
	  assert(it != keepInZones.end());
	  std::shared_ptr<afrl::cmasi::KeepInZone> ptr = it -> second;
	  KeepInZoneMonitor * kizm  = new KeepInZoneMonitor(service_, ptr);
	  this->addMonitor(kizm);
	}
	
	// Start a monitor for allkeep out zones
	for (auto id: ptr -> getKeepOutAreas()){
	  auto it = keepOutZones.find(id);
	  assert(it != keepOutZones.end());
	  std::shared_ptr<afrl::cmasi::KeepOutZone> ptr = it -> second;
	  KeepOutZoneMonitor * kizm  = new KeepOutZoneMonitor(service_, ptr);
	  this->addMonitor(kizm);
	}
        return true;
      }
      bool MonitorDB::processKeepInZone(std::shared_ptr<afrl::cmasi::KeepInZone> ptr){
        
	int64_t zoneID = ptr -> getZoneID();
	assert( keepInZones.find(zoneID) == keepInZones.end()); // Duplicate zoneids are not handled.
	keepInZones.insert(std::pair<int64_t, std::shared_ptr<afrl::cmasi::KeepInZone> >(zoneID, ptr));
        return true;
      }
      bool MonitorDB::processKeepOutZone(std::shared_ptr<afrl::cmasi::KeepOutZone> ptr){
        //KeepOutZoneMonitor * kozm = new KeepOutZoneMonitor(service_, ptr);
        //this -> addMonitor(kozm);
	int64_t zoneID = ptr -> getZoneID();
	assert( keepOutZones.find(zoneID) == keepOutZones.end()); // Duplicate zoneids are not handled.
	keepOutZones.insert(std::pair<int64_t, std::shared_ptr<afrl::cmasi::KeepOutZone> >(zoneID, ptr));
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
	// Check what kind of task it is

	auto ptSearchTask = std::dynamic_pointer_cast<afrl::cmasi::PointSearchTask>(ptr);
	if (ptSearchTask){
	  this -> pointSearchTasks.push_back(ptSearchTask);
	  PointSearchTaskMonitor* pstm = new PointSearchTaskMonitor(this-> service_, ptSearchTask);
	  addMonitor(pstm);
	} else {
	  auto lineSearchTask = std::dynamic_pointer_cast<afrl::cmasi::LineSearchTask>(ptr);
	  if (lineSearchTask){
	    this -> lineSearchTasks.push_back(lineSearchTask);
	    LineSearchTaskMonitor * lstm = new LineSearchTaskMonitor(this -> service_, lineSearchTask);
	    addMonitor(lstm);
	  } else {
	    auto areaSearchTask = std::dynamic_pointer_cast<afrl::cmasi::AreaSearchTask>(ptr);
	    if (areaSearchTask){
	      this -> areaSearchTasks.push_back(areaSearchTask);
	      AreaSearchTaskMonitor * astm = new AreaSearchTaskMonitor(this -> service_, areaSearchTask);
	      addMonitor(astm);
	    }
	  }
	}
        return true;
      }

      
      bool MonitorDB::processTaskCompetionMessage (std::shared_ptr<uxas::messages::task::TaskComplete> ptr){
	return true;
      }
      bool MonitorDB::processTaskCancelMessage(std::shared_ptr<uxas::messages::task::CancelTask> ptr){
	return true;
      }
      bool MonitorDB::processTaskActiveMessage(std::shared_ptr<uxas::messages::task::TaskActive> ptr){
	return true;
      }
      bool MonitorDB::processTaskAssignmentSummary(std::shared_ptr<uxas::messages::task::TaskAssignmentSummary> ptr){
	return true;
      }
	

      
    };
  };
};
