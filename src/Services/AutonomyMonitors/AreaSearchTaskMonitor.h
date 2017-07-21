#ifndef SRC_SERVICES_AUTONOMYMONITORS_AREA_SEARCH_MONITORS_H_
#define SRC_SERVICES_AUTONOMYMONITORS_AREA_SEARCH_MONITORS_H_

#include "AutonomyMonitors/MonitorBase.h"
#include "AutonomyMonitors/AutonomyMonitorServiceMain.h"
#include "afrl/cmasi/AreaSearchTask.h"


namespace uxas {
namespace service {
namespace monitoring {

   class AreaSearchTaskMonitor: public MonitorBase {
  public:

     AreaSearchTaskMonitor(AutonomyMonitorServiceMain * service_ptr, std::shared_ptr<afrl::cmasi::AreaSearchTask> pointSearchTask);
    // GUOHUI: call parent constructor with service_ptr  See KeepOutZoneMonitor.cpp
     ~AreaSearchTaskMonitor();
    void addVehicleStateMessage(VehicleStateMessage const & vMessage);
    bool isPropertySatisfied();
    double propertyRobustness();
  protected:
    std::shared_ptr<afrl::cmasi::AreaSearchTask> _task;
  };


}
}
}


#endif
