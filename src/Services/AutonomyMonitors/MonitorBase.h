/*
 * MonitorBase.h
 *
 *  Created on: Jul 5, 2017
 *      Author: macuser
 */

#ifndef SRC_SERVICES_AUTONOMYMONITORS_MONITORBASE_H_
#define SRC_SERVICES_AUTONOMYMONITORS_MONITORBASE_H_

#include "AutonomyMonitors/AutonomyMonitorServiceMain.h"
#include "VehicleStateMessage.h"

namespace uxas {
namespace service {
namespace monitoring {
/* \class MonitorBase
 * \brief Base class for all the monitors we will use.
 *
 * Each monitor will work as follows.
 * 	We will call the monitor's constructor and then give it all the information it will need.
 * 	Next, we will feed each vehicle state message that we get.
 * 	The monitor will then be able to tell us if the property is true at the end or false.
 * 	We will also ask for "robustness" value for each monitor and later in the next version, allow
 * 	monitors to provide us diagnostic information to explain why a property was violated.
 *
 */
class MonitorBase {
public:
  MonitorBase(AutonomyMonitorServiceMain * service_ptr);
  virtual ~MonitorBase();

  virtual void addVehicleStateMessage(VehicleStateMessage const & vMessage) =0;
  virtual bool isPropertySatisfied() =0;
  virtual double propertyRobustness() = 0;
  /*-- Do nothing --*/
  virtual void sendTaskStatus(){}
  
 protected:
  AutonomyMonitorServiceMain  * service_;
  bool debug;

};

} /* namespace monitoring */
} /* namespace service */
} /* namespace uxas */

#endif /* SRC_SERVICES_AUTONOMYMONITORS_MONITORBASE_H_ */
