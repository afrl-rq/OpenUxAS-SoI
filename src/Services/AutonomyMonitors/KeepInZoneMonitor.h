//
//  KeepInZoneMonitor.h
//  OpenUxAS
//
//  Created by Sriram Sankaranarayanan on 7/11/17.
//
//

#ifndef KeepInZoneMonitor_h
#define KeepInZoneMonitor_h

#include "AutonomyMonitors/MonitorBase.h"
#include "AutonomyMonitors/VehicleStateMessage.h"
#include "afrl/cmasi/KeepInZone.h"
#include "afrl/cmasi/Location3D.h"
#include "afrl/cmasi/AbstractGeometry.h"
#include "afrl/cmasi/AbstractGeometryDescendants.h"

namespace uxas {
    namespace service {
        namespace monitoring {
            class KeepInZoneMonitor: public MonitorBase {
            public:
                KeepInZoneMonitor(std::shared_ptr<afrl::cmasi::KeepInZone> zone);
                ~KeepInZoneMonitor();
                void addVehicleStateMessage(VehicleStateMessage const & vMessage);
                bool isPropertySatisfied();
                double propertyRobustness();
                
            protected:
                std::shared_ptr<afrl::cmasi::KeepInZone> _zone;

                
            };
        };
    };
};
#endif /* KeepInZoneMonitor_h */
