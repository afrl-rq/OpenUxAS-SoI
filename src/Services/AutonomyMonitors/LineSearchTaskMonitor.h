#ifndef SRC_SERVICES_AUTONOMYMONITORS_LINE_SEARCH_MONITORS_H_
#define SRC_SERVICES_AUTONOMYMONITORS_LINE_SEARCH_MONITORS_H_

#include "AutonomyMonitors/MonitorBase.h"
#include "AutonomyMonitors/AutonomyMonitorServiceMain.h"
#include "afrl/cmasi/LineSearchTask.h"


namespace uxas {
namespace service {
namespace monitoring {

   class LineSearchTaskMonitor: public MonitorBase {
  public:

     LineSearchTaskMonitor(AutonomyMonitorServiceMain * service_ptr, std::shared_ptr<afrl::cmasi::LineSearchTask> lineSearchTask);
     ~LineSearchTaskMonitor();
     void addVehicleStateMessage(VehicleStateMessage const & vMessage);
     bool isPropertySatisfied();
     double propertyRobustness();
   protected:
     std::shared_ptr<afrl::cmasi::LineSearchTask> _task;
   };


}
}
}


#endif
