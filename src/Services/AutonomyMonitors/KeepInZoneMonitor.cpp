#include "AutonomyMonitors/KeepInZoneMonitor.h"

namespace uxas {
    namespace service {
        namespace monitoring {
            
            KeepInZoneMonitor::KeepInZoneMonitor(std::shared_ptr<afrl::cmasi::KeepInZone> keepInZone): _zone(keepInZone){}
            
            
            KeepInZoneMonitor::~KeepInZoneMonitor(){}
            
            void KeepInZoneMonitor::addVehicleStateMessage(VehicleStateMessage const & vMessage)
            {
                //TODO: 
            }
            
            bool KeepInZoneMonitor::isPropertySatisfied()
            {
                return true;
            }
            
            double KeepInZoneMonitor::propertyRobustness()
            {
                return 0.0;
            }
            
            
            
        }
    }
}
