/*
 * KeepOutZoneMonitor.h
 *
 *  Created on: Jul 5, 2017
 *      Author: macuser
 */

#ifndef SRC_SERVICES_AUTONOMYMONITORS_KEEPOUTZONEMONITOR_H_
#define SRC_SERVICES_AUTONOMYMONITORS_KEEPOUTZONEMONITOR_H_

#include "Polygon.h"
#include "MonitorBase.h"

namespace uxas {
namespace service {
namespace monitoring {
/** \class KeepOutZoneMonitor
 *  \brief Implements a monitor that given a set of vehicle states checks that none of the states are part of the keepout zone.
 */
class KeepOutZoneMonitor: public MonitorBase {
public:
	KeepOutZoneMonitor(int64_t zoneID);
	virtual ~KeepOutZoneMonitor();

	void keepOutZonePolyhedron(std::vector<int64_t> vehicleIDs, afrl::cmasi::Polygon * p);
	void keepOutZoneRectangle(std::vector<int64_t> vehicleIDs, afrl::cmasi::Rectangle * r);
	void keepOutZoneCircle(std::vector<int64_t> vehicleIDs, afrl::cmasi::Circle * c);

	virtual void addVehicleStateMessage(VehichleStateMessage const & vMessage) =0;
	virtual bool isPropertySatisfied() =0;
	virtual double propertyRobustness() = 0;

protected:


};

} /* namespace monitoring */
} /* namespace service */
} /* namespace uxas */

#endif /* SRC_SERVICES_AUTONOMYMONITORS_KEEPOUTZONEMONITOR_H_ */
