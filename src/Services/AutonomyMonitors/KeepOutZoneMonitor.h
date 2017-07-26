/*
 * KeepOutZoneMonitor.h
 *
 *  Created on: Jul 5, 2017
 *      Author: macuser
 */

#ifndef SRC_SERVICES_AUTONOMYMONITORS_KEEPOUTZONEMONITOR_H_
#define SRC_SERVICES_AUTONOMYMONITORS_KEEPOUTZONEMONITOR_H_

#include "ServiceBase.h"
#include "afrl/cmasi/Polygon.h"
#include "AutonomyMonitors/AutonomyMonitorServiceMain.h"
#include "AutonomyMonitors/MonitorBase.h"
#include "AutonomyMonitors/VehicleStateMessage.h"
#include "afrl/cmasi/KeepOutZone.h"
#include "UnitConversions.h"
namespace uxas {
namespace service {
namespace monitoring {
/** \class KeepOutZoneMonitor
 *  \brief Implements a monitor that given a set of vehicle states checks that none of the states are part of the keepout zone.
 */
class KeepOutZoneMonitor: public MonitorBase {
public:
  KeepOutZoneMonitor(AutonomyMonitorServiceMain * service_ptr, std::shared_ptr<afrl::cmasi::KeepOutZone> keepOutZone);
  virtual ~KeepOutZoneMonitor();
  void addVehicleStateMessage(VehicleStateMessage const & vMessage) override;
  bool isPropertySatisfied() override;
  double propertyRobustness() override;
  void sendTaskStatus() override;
  void sendMonitorStartMessage() override;

protected:
	std::shared_ptr<afrl::cmasi::KeepOutZone> _zone;
	uxas::common::utilities::CUnitConversions flatEarth;
	bool _failed;
	double _robustness;
	void sendFailureMessage(VehicleStateMessage const & vMessage);
      double fail_latitude;
      double fail_longitude;
      double fail_altitude;
      int64_t fail_responsible_vehicle_id;
      int64_t fail_timestamp;
};

} /* namespace monitoring */
} /* namespace service */
} /* namespace uxas */

#endif /* SRC_SERVICES_AUTONOMYMONITORS_KEEPOUTZONEMONITOR_H_ */
