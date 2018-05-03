File: WaypointPlanManagerService.h
Issue:	vehicleID can be overwritten from configuration file for unknown reason.
Lines:	81-84
Resolution:  If UxAS is run in centralized mode, the entityID is filled with a non-realistic entitity ID.  Separate instances of the WaypointPlanManagerService must be used to distinguish vehicle waypoints that must be stated via configuration file parameter.






