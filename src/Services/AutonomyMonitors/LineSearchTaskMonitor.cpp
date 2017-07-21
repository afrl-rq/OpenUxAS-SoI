#include "AutonomyMonitors/LineSearchTaskMonitor.h"


namespace uxas {
namespace service {
namespace monitoring {
  
  LineSearchTaskMonitor::LineSearchTaskMonitor(AutonomyMonitorServiceMain * service_ptr, std::shared_ptr<afrl::cmasi::LineSearchTask> pointSearchTask):MonitorBase(service_ptr), _task(pointSearchTask){};

  LineSearchTaskMonitor::~LineSearchTaskMonitor(){};

  void LineSearchTaskMonitor::addVehicleStateMessage(VehicleStateMessage const & vMessage){
  }

  bool LineSearchTaskMonitor::isPropertySatisfied(){
    return true;
  }

  double LineSearchTaskMonitor::propertyRobustness(){
    return 0.0;
  }
  
}
}
}
