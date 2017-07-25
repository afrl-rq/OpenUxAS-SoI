#ifndef SRC_SERVICES_AUTONOMYMONITORS_LINE_SEARCH_MONITORS_H_
#define SRC_SERVICES_AUTONOMYMONITORS_LINE_SEARCH_MONITORS_H_

#include "AutonomyMonitors/MonitorBase.h"
#include "AutonomyMonitors/AutonomyMonitorServiceMain.h"
#include "AutonomyMonitors/GeometryUtilities.h"
#include "afrl/cmasi/LineSearchTask.h"
#include "afrl/cmasi/Location3D.h"
#include "UnitConversions.h"

namespace uxas {
namespace service {
namespace monitoring {

  class LineSearchTaskMonitor: public MonitorBase {

  public:
    LineSearchTaskMonitor(AutonomyMonitorServiceMain * service_ptr,
			  std::shared_ptr<afrl::cmasi::LineSearchTask> lineSearchTask);
    ~LineSearchTaskMonitor();
    void addVehicleStateMessage(VehicleStateMessage const & vMessage);
    bool isPropertySatisfied();
    double propertyRobustness();
    void sendTaskStatus();
    
  protected:
    std::shared_ptr<afrl::cmasi::LineSearchTask> _task;
    uxas::common::utilities::CUnitConversions flatEarth;
    std::vector<LineSegment> segments;

  };

  
  

}
}
}


#endif
