/*
 * KeepOutZoneMonitor.h
 *
 *  Created on: Jul 5, 2017
 *      Author: macuser
 */

#ifndef SRC_SERVICES_AUTONOMYMONITORS_KEEPOUTZONEMONITOR_H_
#define SRC_SERVICES_AUTONOMYMONITORS_KEEPOUTZONEMONITOR_H_

#include "afrl/cmasi/Polygon.h"
#include "AutonomyMonitors/MonitorBase.h"
#include "AutonomyMonitors/VehicleStateMessage.h"
#include "afrl/cmasi/KeepOutZone.h"

namespace uxas {
namespace service {
namespace monitoring {
/** \class KeepOutZoneMonitor
 *  \brief Implements a monitor that given a set of vehicle states checks that none of the states are part of the keepout zone.
 */
class KeepOutZoneMonitor: public MonitorBase {
public:
	KeepOutZoneMonitor(std::shared_ptr<afrl::cmasi::KeepOutZone> keepOutZone);
	virtual ~KeepOutZoneMonitor();
	void addVehicleStateMessage(VehicleStateMessage const & vMessage);
	bool isPropertySatisfied();
	double propertyRobustness();

protected:
	std::shared_ptr<afrl::cmasi::KeepOutZone> _zone;

};

} /* namespace monitoring */
} /* namespace service */
} /* namespace uxas */

#endif /* SRC_SERVICES_AUTONOMYMONITORS_KEEPOUTZONEMONITOR_H_ */
