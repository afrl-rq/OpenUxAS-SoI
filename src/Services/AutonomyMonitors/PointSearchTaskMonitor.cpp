#include "AutonomyMonitors/PointSearchTaskMonitor.h"


namespace uxas {
namespace service {
namespace monitoring {
  
  PointSearchTaskMonitor::PointSearchTaskMonitor(AutonomyMonitorServiceMain * service_ptr, std::shared_ptr<afrl::cmasi::PointSearchTask> pointSearchTask):MonitorBase(service_ptr), _task(pointSearchTask){};

  PointSearchTaskMonitor::~PointSearchTaskMonitor(){};

  void PointSearchTaskMonitor::addVehicleStateMessage(VehicleStateMessage const & vMessage){
  }

  bool PointSearchTaskMonitor::isPropertySatisfied(){
    return true;
  }

  double PointSearchTaskMonitor::propertyRobustness(){
    return 0.0;
  }
  
}
}
}
