/*
* AutonomyMonitorServiceMain.cpp
*
*  Created on: Jul 2, 2017
*      Author: macuser
*/

#include "ServiceBase.h"
#include "AutonomyMonitors/AutonomyMonitorServiceMain.h"

#include "afrl/cmasi/AirVehicleState.h"
#include "afrl/cmasi/AirVehicleConfiguration.h"
#include "uxas/messages/task/UniqueAutomationRequest.h"
#include "uxas/messages/task/UniqueAutomationResponse.h"
#include "afrl/cmasi/EntityState.h"
#include "afrl/cmasi/KeepInZone.h"
#include "afrl/cmasi/KeepOutZone.h"
#include "afrl/cmasi/Task.h"
#include "afrl/cmasi/TaskDescendants.h"
#include "uxas/messages/task/TaskComplete.h"
#include "uxas/messages/task/CancelTask.h"
#include "uxas/messages/task/TaskActive.h"
#include "uxas/messages/task/TaskAssignmentSummary.h"

#include "afrl/impact/PointOfInterest.h"
#include "afrl/impact/LineOfInterest.h"
#include "afrl/impact/AreaOfInterest.h"
#include "MonitorDB.h"

#include <sstream>      //std::stringstream
#include <iostream>     // std::cout, cerr, etc
#include <fstream>     // std::ifstream
#include <cstdint>
#include <memory>      //int64_t
#include <iomanip>      //setfill
#include <map>


#define STRING_COMPONENT_NAME "AutomationMonitorService"
#define STRING_XML_COMPONENT_TYPE STRING_COMPONENT_NAME
#define STRING_XML_COMPONENT "Component"
#define STRING_XML_TYPE "Type"


namespace uxas {
  namespace service {
    namespace monitoring {

      AutonomyMonitorServiceMain::ServiceBase::CreationRegistrar<AutonomyMonitorServiceMain>
      AutonomyMonitorServiceMain::s_registrar(AutonomyMonitorServiceMain::s_registryServiceTypeNames());

      // Constructor.
      AutonomyMonitorServiceMain::AutonomyMonitorServiceMain()
	: ServiceBase (AutonomyMonitorServiceMain::s_typeName(),
		    AutonomyMonitorServiceMain::s_directoryName()),
	  monitorDB(new MonitorDB(this))
      {        
      };

      // Destructor.
      AutonomyMonitorServiceMain::~AutonomyMonitorServiceMain() {
	delete(monitorDB);
      };

      //Configuration
      bool AutonomyMonitorServiceMain::configure(const pugi::xml_node & ndComponent){
        // Messages to subscribe to AirVehicleConfiguration
        addSubscriptionAddress(afrl::cmasi::AirVehicleConfiguration::Subscription);
        // AirVehicleState
        addSubscriptionAddress(afrl::cmasi::AirVehicleState::Subscription);
        // AutomationRequest
        addSubscriptionAddress(uxas::messages::task::UniqueAutomationRequest::Subscription);
        // AutomationResponse
        addSubscriptionAddress(uxas::messages::task::UniqueAutomationResponse::Subscription);
        // Boundaries
        addSubscriptionAddress(afrl::cmasi::OperatingRegion::Subscription);
        addSubscriptionAddress(afrl::cmasi::KeepOutZone::Subscription);
        addSubscriptionAddress(afrl::cmasi::KeepInZone::Subscription);
        // Task Based Messages
	addSubscriptionAddress(uxas::messages::task::TaskComplete::Subscription);
	addSubscriptionAddress(uxas::messages::task::CancelTask::Subscription);
	addSubscriptionAddress(uxas::messages::task::TaskActive::Subscription);
	addSubscriptionAddress(uxas::messages::task::TaskAssignmentSummary::Subscription);
       

        // Subscribe to Task and all derivatives of Task (copied from AutomationDiagramDataService.cpp)
        addSubscriptionAddress(afrl::cmasi::Task::Subscription);
        std::vector< std::string > childtasks = afrl::cmasi::TaskDescendants();
        for(auto child : childtasks)
        addSubscriptionAddress(child);
        return true;
      }

      bool AutonomyMonitorServiceMain::start(){
        std::cout << "[Autonomy Monitoring Service Started]" << std::endl;
        return true;
      }

      bool AutonomyMonitorServiceMain::terminate(){
        std::cout << "[Autonomy Monitoring Service Terminated]" << std::endl;
        return true;
      }

      bool
      AutonomyMonitorServiceMain::initialize()
      {
        bool isSuccess{true};
        return (isSuccess);
      }

      void AutonomyMonitorServiceMain::broadcastMessage(const std::shared_ptr<avtas::lmcp::Object>  & msgToBroadcast) {
	sendSharedLmcpObjectBroadcastMessage(msgToBroadcast);
      }
      
      #define PTR_CAST_TYP(t, o) (std::dynamic_pointer_cast<t>(o -> m_object))

      bool
      AutonomyMonitorServiceMain::processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage)
      {

        auto entityState = std::dynamic_pointer_cast<afrl::cmasi::EntityState>(receivedLmcpMessage -> m_object);
        if (entityState){
          monitorDB -> processEntityState(entityState);
          return (false);
        }


        auto entityConfig = std::dynamic_pointer_cast<afrl::cmasi::EntityConfiguration>(receivedLmcpMessage -> m_object);
        if (entityConfig){
          monitorDB -> processEntityConfiguration(entityConfig);
          return (false);
        }



        auto uniqueAutReq = std::dynamic_pointer_cast<uxas::messages::task::UniqueAutomationRequest>(receivedLmcpMessage -> m_object);
        if (uniqueAutReq){
          monitorDB -> processUniqueAutomationRequest(uniqueAutReq);
          return (false);
        }

        auto uniqueAutResp = std::dynamic_pointer_cast<uxas::messages::task::UniqueAutomationResponse>(receivedLmcpMessage -> m_object);
        if (uniqueAutResp){
          monitorDB -> processUniqueAutomationResponse(uniqueAutResp);
          return (false);
        }

        auto opRegion = PTR_CAST_TYP(afrl::cmasi::OperatingRegion, receivedLmcpMessage);
        if (opRegion){
          monitorDB -> processOperatingRegion(opRegion);
          return false;
        }

        auto keepOutZone = PTR_CAST_TYP(afrl::cmasi::KeepOutZone, receivedLmcpMessage);
        if (keepOutZone){
          monitorDB -> processKeepOutZone(keepOutZone);
          return false;
        }

        auto keepInZone = PTR_CAST_TYP(afrl::cmasi::KeepInZone, receivedLmcpMessage);
        if (keepInZone){
          monitorDB -> processKeepInZone(keepInZone);
          return false;
        }

	auto tCompleteMsg = PTR_CAST_TYP(uxas::messages::task::TaskComplete, receivedLmcpMessage);
	if (tCompleteMsg){
	  monitorDB -> processTaskCompetionMessage(tCompleteMsg);
	  return false;
	}
	auto tActiveMsg = PTR_CAST_TYP(uxas::messages::task::TaskActive, receivedLmcpMessage);

	if (tActiveMsg){
	  monitorDB -> processTaskActiveMessage(tActiveMsg);
	  return false;
	}
	auto tCancelMsg = PTR_CAST_TYP(uxas::messages::task::CancelTask, receivedLmcpMessage);

	if (tCancelMsg){
	  monitorDB -> processTaskCancelMessage(tCancelMsg);
	  return false;
	}
	auto tAssignmentSummary = PTR_CAST_TYP(uxas::messages::task::TaskAssignmentSummary, receivedLmcpMessage);
	if (tAssignmentSummary){
	  monitorDB -> processTaskAssignmentSummary(tAssignmentSummary);
	  return false;
	}
	

        // auto areaOfInterest = PTR_CAST_TYP(afrl::impact::AreaOfInterest, receivedLmcpMessage);
        // if (areaOfInterest){
        //   monitorDB -> processAreaOfInterest(areaOfInterest);
        //   return false;
        // }

        // auto lineOfInterest = PTR_CAST_TYP(afrl::impact::LineOfInterest, receivedLmcpMessage);
        // if (lineOfInterest){
        //   monitorDB -> processLineOfInterest(lineOfInterest);
        //   return false;
        // }

        // auto pointOfInterest = PTR_CAST_TYP(afrl::impact::PointOfInterest, receivedLmcpMessage);
        // if (pointOfInterest){
        //   monitorDB -> processPointOfInterest(pointOfInterest);
        //   return false;
        // }

	

        auto task = PTR_CAST_TYP(afrl::cmasi::Task, receivedLmcpMessage);
        if (task){
          monitorDB -> processTask(task);
          return false;
        }

        return (false);
      }




    } /* namespace monitoring */
  } /* namespace service */
} /* namespace uxas */
