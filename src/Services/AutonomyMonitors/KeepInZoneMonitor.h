//
//  KeepInZoneMonitor.h
//  OpenUxAS
//
//  Created by Sriram Sankaranarayanan on 7/11/17.
//
//

#ifndef KeepInZoneMonitor_h
#define KeepInZoneMonitor_h

#include "ServiceBase.h"
#include "AutonomyMonitors/MonitorBase.h"
#include "AutonomyMonitors/AutonomyMonitorServiceMain.h"
#include "AutonomyMonitors/VehicleStateMessage.h"
#include "afrl/cmasi/KeepInZone.h"
#include "afrl/cmasi/Location3D.h"
#include "afrl/cmasi/AbstractGeometry.h"
#include "afrl/cmasi/AbstractGeometryDescendants.h"
#include "afrl/cmasi/autonomymonitor/OperatingZoneFailure.h"
#include "afrl/cmasi/autonomymonitor/OperatingZoneFailureType.h"
#include "afrl/cmasi/autonomymonitor/OperatingZoneSuccess.h"
#include "UnitConversions.h"

namespace uxas {
namespace service {
namespace monitoring {
class KeepInZoneMonitor: public MonitorBase {
public:
      KeepInZoneMonitor(AutonomyMonitorServiceMain  *service_ptr, std::shared_ptr<afrl::cmasi::KeepInZone> zone);
      ~KeepInZoneMonitor();
      void sendMonitorStartMessage() override;
      void addVehicleStateMessage(VehicleStateMessage const & vMessage) override;
      bool isPropertySatisfied() override;
      double propertyRobustness() override;
      void sendTaskStatus() override;
      void sendFailureMessage(VehicleStateMessage const & vMessage);

protected:
      std::shared_ptr<afrl::cmasi::KeepInZone> _zone;
      bool _failed;
      uxas::common::utilities::CUnitConversions flatEarth;
      double fail_latitude;
      double fail_longitude;
      int64_t fail_responsible_vehicle_id;
      int64_t fail_timestamp;
      double fail_altitude;
      double _robustness;
};
};
};
};
#endif /* KeepInZoneMonitor_h */
