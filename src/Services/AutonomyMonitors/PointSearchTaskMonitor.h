
#ifndef SRC_SERVICES_AUTONOMYMONITORS_POINT_SEARCH_MONITORS_H_
#define SRC_SERVICES_AUTONOMYMONITORS_POINT_SEARCH_MONITORS_H_

#include "AutonomyMonitors/MonitorBase.h"
#include "AutonomyMonitors/AutonomyMonitorServiceMain.h"

namespace uxas {
namespace service {
namespace monitoring {

  class PointSearchTaskMonitor: public MonitorBase {
  public:

    PointSearchTaskMonitor(AutonomyMonitorServiceMain * service_ptr, std::shared_ptr<afrl::cmasi::PointSearchTask> pointSearchTask):MonitorBase(service_ptr), _task(pointSearchTask){}
    // GUOHUI: call parent constructor with service_ptr  See KeepOutZoneMonitor.cpp
    void addVehicleStateMessage(VehicleStateMessage const & vMessage);
    bool isPropertySatisfied();
    double propertyRobustness();
  protected:
    std::shared_ptr<afrl::cmasi::PointSearchTask> _task;
  };

};
};
};


#endif
