#ifndef D__MONITOR__DB__
#define D__MONITOR__DB__


#include <iostream>
#include <map>
#include <vector>
#include <memory>
#include "ServiceBase.h"
#include "afrl/cmasi/AirVehicleState.h"
#include "afrl/cmasi/AirVehicleConfiguration.h"
#include "afrl/cmasi/OperatingRegion.h"
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

#include "AutonomyMonitors/AutonomyMonitorServiceMain.h"
#include "AutonomyMonitors/VehicleStateMessage.h"
#include "AutonomyMonitors/MonitorBase.h"

namespace uxas {
  namespace service {
    namespace monitoring {

      /** \class MonitorDB
      *  \brief This class will keep the relevant data needed for the monitoring in one place.
      *  <b>
      *  The main purpose of this class is to store the necessary data in terms of the automation
      *  requests/responses and the vehicle states to judge success or failure of the mission requirements
      *  and the overall plan.
      **/
      
      class MonitorDB {
      private:
        std::vector<MonitorBase*> allMonitors;
        std::vector<VehicleStateMessage> allVehicleStateMessages;
	AutonomyMonitorServiceMain * service_;
	
	std::map<int64_t, std::shared_ptr<afrl::cmasi::KeepOutZone> > keepOutZones;
	std::map<int64_t, std::shared_ptr<afrl::cmasi::KeepInZone> > keepInZones;
	std::vector<std::shared_ptr<afrl::cmasi::PointSearchTask> > pointSearchTasks;
	std::vector<std::shared_ptr<afrl::cmasi::LineSearchTask> > lineSearchTasks;
	std::vector<std::shared_ptr<afrl::cmasi::AreaSearchTask> > areaSearchTasks;
	
      public:
        /* Default Constructor */
        MonitorDB(AutonomyMonitorServiceMain * service_ptr);
        /* Destructor */
        virtual ~MonitorDB();

        /*-- Functions to record and parse automation related messages --*/
        bool processEntityState(std::shared_ptr<afrl::cmasi::EntityState> ptr);
        bool processEntityConfiguration(std::shared_ptr<afrl::cmasi::EntityConfiguration> ptr);
        bool processUniqueAutomationRequest(std::shared_ptr<uxas::messages::task::UniqueAutomationRequest> ptr);
        bool processUniqueAutomationResponse(std::shared_ptr<uxas::messages::task::UniqueAutomationResponse> ptr);
        bool processOperatingRegion(std::shared_ptr<afrl::cmasi::OperatingRegion> ptr);
        bool processKeepInZone(std::shared_ptr<afrl::cmasi::KeepInZone> ptr);
        bool processKeepOutZone(std::shared_ptr<afrl::cmasi::KeepOutZone> ptr);
        bool processAreaOfInterest(std::shared_ptr<afrl::impact::AreaOfInterest> ptr);
        bool processLineOfInterest(std::shared_ptr<afrl::impact::LineOfInterest> ptr);
        bool processPointOfInterest(std::shared_ptr<afrl::impact::PointOfInterest> ptr);
        bool processTask(std::shared_ptr<afrl::cmasi::Task> ptr);

        /*-- Setup the required monitors --*/

        /*-- Monitor/Judge task completion status --*/

      protected:
        void registerVehicleState(VehicleStateMessage  vMessage);
        void addMonitor(MonitorBase * what) ;


      };
    };
  };
};
#endif
