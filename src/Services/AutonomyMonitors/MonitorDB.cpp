
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


#include "UxAS_Log.h"

namespace uxas {
  namespace service {
    namespace monitoring {

      MonitorDB::MonitorDB(AutonomyMonitorServiceMain  * service_ptr): service_(service_ptr) {};
      MonitorDB::~MonitorDB() {
	for (auto m: allMonitors){
	  delete(m);
	}

	for (auto it = taskMonitorsByTaskID.begin(); it != taskMonitorsByTaskID.end(); ++it){
	  delete(it -> second);
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
	int64_t vehicle_id = vMessage.getVehicleID();
	auto it= taskMonitorsByVehicleID.find(vehicle_id);
	if (it != taskMonitorsByVehicleID.end()){
	  auto & v = it -> second;
	  for (MonitorBase * mon: v){
	    mon -> addVehicleStateMessage(vMessage);
	  }
	} else {
	  UXAS_LOG_WARN("[AutonomyMonitor]: Vehicle ID: ", vehicle_id, " is not associated with any task at this time.");
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
	// For now just record the operating region
	int64_t id = ptr -> getID();
	this -> allOperatingRegions[id] = ptr;
	return true;
      }

      void MonitorDB::createMonitorsForOperatingRegion(int64_t regionID){
	auto it = allOperatingRegions.find(regionID);
	assert( it != allOperatingRegions.end());
	std::shared_ptr<afrl::cmasi::OperatingRegion> ptr = it -> second;
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
        return;
      }

      
      bool MonitorDB::processKeepInZone(std::shared_ptr<afrl::cmasi::KeepInZone> ptr){
        
	int64_t zoneID = ptr -> getZoneID();
	assert( keepInZones.find(zoneID) == keepInZones.end()); // Duplicate zoneids are not handled.
	keepInZones.insert(std::pair<int64_t,
			   std::shared_ptr<afrl::cmasi::KeepInZone> >(zoneID, ptr));
        return true;
      }

      bool MonitorDB::processKeepOutZone(std::shared_ptr<afrl::cmasi::KeepOutZone> ptr){
	int64_t zoneID = ptr -> getZoneID();
	assert( keepOutZones.find(zoneID) == keepOutZones.end()); // Duplicate zoneids are not handled.
	keepOutZones.insert(std::pair<int64_t,
			    std::shared_ptr<afrl::cmasi::KeepOutZone> >(zoneID, ptr));
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
	bool taskRecognized = false;
	int64_t task_id = ptr -> getTaskID();

	
	if (!taskRecognized){
	  auto ptSearchTask = std::dynamic_pointer_cast<afrl::cmasi::PointSearchTask>(ptr);
	  if (ptSearchTask){
	    pointSearchTasks[task_id] = ptSearchTask;
	    taskRecognized = true;
	  }
	}
	
	if (!taskRecognized) {
	  auto lineSearchTask = std::dynamic_pointer_cast<afrl::cmasi::LineSearchTask>(ptr);
	  if (lineSearchTask){
	    lineSearchTasks[task_id] = lineSearchTask;
	    taskRecognized = true;
	  }
	}

	if (!taskRecognized){
	  auto areaSearchTask = std::dynamic_pointer_cast<afrl::cmasi::AreaSearchTask>(ptr);
	  if (areaSearchTask){
	    areaSearchTasks[task_id] = areaSearchTask;
	    taskRecognized = true;
	  }
	}

	if (!taskRecognized){
	  UXAS_LOG_WARN("[AutonomyMonitor]: MonitorDB::processTask -- task ID ", task_id,
			" belongs to a type that is not handled in our monitoring yet. ");
	}
        return true;
      }

      void MonitorDB::addTaskMonitorForVehicle(int64_t vehicleID, int64_t taskID, MonitorBase * mon){
	auto it = taskMonitorsByTaskID.find(taskID);
	assert (it == taskMonitorsByTaskID.end());
	taskMonitorsByTaskID[taskID] = mon;

	auto jt = taskMonitorsByVehicleID.find(vehicleID);
	if (jt == taskMonitorsByVehicleID.end()){
	  std::vector<MonitorBase*> v{mon};
	  taskMonitorsByVehicleID[vehicleID] = v;
	} else {
	  jt -> second.push_back(mon);
	}
	return;
      }
      
      void MonitorDB::createMonitorForTask(messages::task::TaskAssignment * ta){
	int64_t taskID = ta -> getTaskID();
	int64_t assignedVehicleID = ta -> getAssignedVehicle();

	UXAS_LOG_INFORM("[AutonomyMonitor]: Task start and end time constraints are not handled inside the AutonomyMonitor");
	bool taskRecognized = false;

	if (!taskRecognized){
	  auto it = pointSearchTasks.find(taskID);
	  if (it != pointSearchTasks.end()){
	    auto ptr = it -> second;
	    taskRecognized=true;
	    PointSearchTaskMonitor * pstm = new PointSearchTaskMonitor(service_, ptr);
	    addTaskMonitorForVehicle(assignedVehicleID, taskID, pstm);
	  }
	}

	if (!taskRecognized){
	  auto it = lineSearchTasks.find(taskID);
	  if (it != lineSearchTasks.end()){
	    auto lstask = it -> second;
	    taskRecognized = true;
	    LineSearchTaskMonitor * lstm = new LineSearchTaskMonitor(service_, lstask);
	    addTaskMonitorForVehicle(assignedVehicleID, taskID, lstm);
	  }
	}

	if (!taskRecognized){
	  auto it = areaSearchTasks.find(taskID);
	  if (it != areaSearchTasks.end()){
	    auto astask = it -> second;
	    taskRecognized = true;
	    AreaSearchTaskMonitor * astm = new AreaSearchTaskMonitor(service_, astask);
	    addTaskMonitorForVehicle(assignedVehicleID, taskID, astm);
	  }
	}
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
	/*-- Record the task assignments --*/
	int64_t opRegionID = ptr -> getOperatingRegion();
	createMonitorsForOperatingRegion(opRegionID);
	std::vector<messages::task::TaskAssignment*> assignedTasks = ptr -> getTaskList();
	for (auto ta: assignedTasks){
	  createMonitorForTask(ta);
	}
	return true;
      }
	

      
    };
  };
};
