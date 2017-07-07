#ifndef D__MONITOR__DB__
#define D__MONITOR__DB__


#include <iostream>
#include <map>
#include <vector>
#include <memory>

#include "afrl/cmasi/AirVehicleState.h"
#include "afrl/cmasi/AirVehicleConfiguration.h"
#include "afrl/cmasi/UniqueAutomationRequest.h"
#include "afrl/cmasi/EntityState.h"
#include "afrl/cmasi/KeepInZone.h"
#include "afrl/cmasi/KeepOutZone.h"
#include "afrl/cmasi/Task.h"
#include "afrl/cmasi/TaskDescendants.h"

#include "afrl/impact/PointOfInterest.h"
#include "afrl/impact/LineOfInterest.h"
#include "afrl/impact/AreaOfInterest.h"

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
      protected:
        shared_ptr<afrl::cmasi::EntityState>
      public:
        /* Default Constructor */
        MonitorDB();
        /* Destructor */
        virtual ~MonitorDB();

        /*-- Functions to record and parse automation related messages --*/
        bool processEntityState(std::shared_ptr<afrl::cmasi::EntityState> ptr);
        bool processEntityConfiguration(std::shared_ptr<afrl::cmasi::EntityConfiguration> ptr);
        bool processUniqueAutomationRequest(std::shared_ptr<afrl::messages::task::UniqueAutomationRequest> ptr);
        bool processUniqueAutomationResponse(std::shared_ptr<afrl::messages::task::UniqueAutomationResponse> ptr);
        bool processOperatingRegion(std::shared_ptr<afrl::cmasi::OperatingRegion> ptr);
        bool processKeepInZone(std::shared_ptr<afrl::cmasi::KeepInZone> ptr);
        bool processKeepOutZone(std::shared_ptr<afrl::cmasi::KeepOutZone> ptr);
        bool processAreaOfInterest(std::shared_ptr<afrl::impact::AreaOfInterest> ptr);
        bool processLineOfInterest(std::shared_ptr<afrl::impact::LineOfInterest> ptr);
        bool processPointOfInterest(std::shared_ptr<afrl::impact::PointOfInterest> ptr);
        bool processTask(std::shared_ptr<afrl::cmasi::Task> ptr);

        /*-- Setup the required monitors --*/

        /*-- Monitor/Judge task completion status --*/

      };
    };
  };
};
#endif
