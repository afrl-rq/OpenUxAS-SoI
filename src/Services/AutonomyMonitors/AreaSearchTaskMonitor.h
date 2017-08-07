#ifndef SRC_SERVICES_AUTONOMYMONITORS_AREA_SEARCH_MONITORS_H_
#define SRC_SERVICES_AUTONOMYMONITORS_AREA_SEARCH_MONITORS_H_

#include "AutonomyMonitors/MonitorBase.h"
#include "AutonomyMonitors/AutonomyMonitorServiceMain.h"
#include "afrl/cmasi/AreaSearchTask.h"

#include "UnitConversions.h"
#include <math.h>


namespace uxas {
  namespace service {
    namespace monitoring {

      class AreaSearchTaskMonitor: public MonitorBase {
      public:

        AreaSearchTaskMonitor(AutonomyMonitorServiceMain * service_ptr, std::shared_ptr<afrl::cmasi::AreaSearchTask> areaSearchTask);
        // GUOHUI: call parent constructor with service_ptr  See KeepOutZoneMonitor.cpp
        ~AreaSearchTaskMonitor();
        void addVehicleStateMessage(VehicleStateMessage const & vMessage);
        bool isPropertySatisfied();
        double propertyRobustness();
        void sendMonitorStartMessage();
        
      protected:
        std::shared_ptr<afrl::cmasi::AreaSearchTask> _task;
        uxas::common::utilities::CUnitConversions flatEarth;
        double innerCircleRadius; // for each point in viewAnglelist, it has the inner circle radius
        double ExpandMoat; // the expanded distance of the convex hull
        double _robustness;
      };
    }
  }
}


#endif
