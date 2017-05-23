
## AutomationRequestValidatorService

This service provides a simple sanity check on external automation requests. It also
queues requests and tags them with unique identifiers, feeding them into the system
one at a time.

This service has two states: **idle** and **busy**. In both states, when a non *AutomationRequest*
message is received, a local memory store is updated to maintain a list of all available
tasks, vehicle configurations, vehicle states, zones, and operating regions.

Upon reception of an *AutomationRequest* message, this service ensures that such a request
can be carried out by checking its local memory store for existence of the requested
vehicles, tasks, and operating region. If the request includes vehicles, tasks, or an
operating region that has not previously been defined, this service will publish an error
message.

Upon determination that the *AutomationRequest* includes only vehicles, tasks, and an
operating region that have previously been defined, this service creates a
*UniqueAutomationRequest* with a previously unused unique identifier. If in the
**idle** state, this service will immediately publish the *UniqueAutomationRequest*
message and transition to the **busy** state. If already in the **busy** state,
the *UniqueAutomationRequest* will be added to the end of a queue.

When this service receives either an error message (indicating that the *UniqueAutomationRequest*
cannot be fulfilled or a corresponding *UniqueAutomationResponse*), it will publish
the same message. If in the **idle** state, it will remain in the **idle** state. If
in the **busy** state, it will remove from the queue the request that was just fulfilled and
then send the next *UniqueAutomationRequest* in the queue. If the queue is empty, this
service transitions back to the **idle** state.

This service also includes a parameter that allows an optional *timeout* value to be set.
When a *UniqueAutomationRequest* is published, a timer begins. If the *timeout* has been reached
before a *UniqueAutomationResponse* is received, an error is assumed to have occured and this
service removes the pending *UniqueAutomationRequest* from the queue and attempts to send the
next in the queue or transition to **idle** if the queue is empty.


: Table of messages that the *AutomationRequestValidatorService* receives and processes.

+----------------------------+---------------------------------------------------------------+
| Message Subscription       | Description                                                   |
+============================+===============================================================+
| *AutomationRequest*        | Primary message to request a set of Tasks to be completed     |
|                            | by a set of vehicles in a particular airspace configuration   |
|                            | (described by an *OperatingRegion*).                          |
+----------------------------+---------------------------------------------------------------+
| *EntityConfiguration*      | Vehicle capabilities (e.g. allowable speeds) are described    |
|                            | by entity configuration messages. Any vehicle requested in    |
|                            | an *AutomationRequest* must previously be described by an     |
|                            | associated *EntityConfiguration*.                             |
+----------------------------+---------------------------------------------------------------+
| *EntityState*              | Describes the actual state of a vehicle in the system         |
|                            | including position, speed, and fuel status. Each vehicle in   |
|                            | an *AutomationRequest* must have reported its state.          |
+----------------------------+---------------------------------------------------------------+
| *Task*                     | Details a particular task that will be referenced (by ID) in  |
|                            | an *AutomationRequest*.                                       |
+----------------------------+---------------------------------------------------------------+
| *TaskInitialized*          | Indicates that a particular task is ready to proceed with the |
|                            | task assignment sequence. Each task requested in              |
|                            | the *AutomationRequest* must be initialized before a          |
|                            | *UniqueAutomationRequest* is published.                       |
+----------------------------+---------------------------------------------------------------+
| *KeepInZone*               | Polygon description of a region in which vehicles must not    |
|                            | travel. If referenced by the *OperatingRegion* in the         |
|                            | *AutomationRequest*, zone must exist for request to be valid. |
+----------------------------+---------------------------------------------------------------+
| *KeepOutZone*              | Polygon description of a region in which vehicles must remain |
|                            | during travel. If referenced by the *OperatingRegion* in the  |
|                            | *AutomationRequest*, zone must exist for request to be valid. |
+----------------------------+---------------------------------------------------------------+
| *OperatingRegion*          | Collection of *KeepIn* and *KeepOut* zones that describe the  |
|                            | allowable space for vehicular travel. Must be defined for     |
|                            | *AutomationRequest* to be valid.                              |
+----------------------------+---------------------------------------------------------------+
| *UniqueAutomationResponse* | Completed response from the rest of the task assignment       |
|                            | process. Indicates that the next *AutomationRequest* is ready |
|                            | to be processed.                                              |
+----------------------------+---------------------------------------------------------------+


: Table of messages that the *AutomationRequestValidatorService* publishes.

+----------------------------+---------------------------------------------------------------+
| Message Publication        | Description                                                   |
+============================+===============================================================+
| *UniqueAutomationRequest*  | A duplicate message to an external *AutomationRequest* but    |
|                            | only published if the request is determined to be valid. Also |
|                            | includes a unique identifier to match to the corresponding    |
|                            | response.                                                     |
+----------------------------+---------------------------------------------------------------+
| *ServiceStatus*            | Error message when a request is determined to be invalid.     |
|                            | Includes human readable error message that highlights which   |
|                            | portion of the *AutomationRequest* was invalid.               |
+----------------------------+---------------------------------------------------------------+
| *AutomationResponse*       | Upon reception of a completed *UniqueAutomationResponse*,     |
|                            | this message is published as a response to the original       |
|                            | request.                                                      |
+----------------------------+---------------------------------------------------------------+


## TaskManagerService

The *TaskManagerService* is a very straight-forward service. Upon reception of a Task message,
it will send the appropriate *CreateNewService* message. To do so, it catalogues all entity
configurations and current states; areas, lines, and points of interest; and current waypoint
paths for each vehicle. This information is stored in local memory and appended as part of
the *CreateNewService* message which allows new Tasks to immediately be informed of all
relevant information needed to carry out a Task.

When *TaskManagerService* receives a *RemoveTasks* message, it will form the appropriate
*KillService* message to properly destroy the service that was created to fulfill the
original Task. 


: Table of messages that the *TaskManagerService* receives and processes.

+----------------------------+---------------------------------------------------------------+
| Message Subscription       | Description                                                   |
+============================+===============================================================+
| *Task*                     | Primary message that describes a particular task. The task    |
|                            | manager will make the appropriate service creation message    |
|                            | to build a service that directly handles this requested Task. |
+----------------------------+---------------------------------------------------------------+
| *RemoveTasks*              | Indicates that Task is no longer needed and will not be       |
|                            | included in future *AutomationRequest* messages. Task manager |
|                            | will send the proper *KillService* message to remove the      |
|                            | service that was constructed to handle the requested Task.    |
+----------------------------+---------------------------------------------------------------+
| *EntityConfiguration*      | Vehicle capabilities (e.g. allowable speeds) are described    |
|                            | by entity configuration messages. New Tasks are informed of   |
|                            | all known entities upon creation.                             |
+----------------------------+---------------------------------------------------------------+
| *EntityState*              | Describes the actual state of a vehicle in the system         |
|                            | including position, speed, and fuel status. New Tasks are     |
|                            | informed of all known entity states upon creation.            |
+----------------------------+---------------------------------------------------------------+
| *AreaOfInterest*           | Describes known geometries of areas, lines, and points. New   |
| *LineOfInterest*           | Tasks are informed of all such named areas upon creation.     |
| *PointOfInterest*          |                                                               |
+----------------------------+---------------------------------------------------------------+
| *MissionCommand*           | Describes current set of waypoints that a vehicle is          |
|                            | following. New Tasks are informed of all known current        |
|                            | waypoint routes upon creation.                                |
+----------------------------+---------------------------------------------------------------+



: Table of messages that the *TaskManagerService* publishes.

+----------------------------+---------------------------------------------------------------+
| Message Publication        | Description                                                   |
+============================+===============================================================+
| *CreateNewService*         | Primary message published by the Task Manager to dynamically  |
|                            | build a new Task from an outside description of such a Task.  |
+----------------------------+---------------------------------------------------------------+
| *KillService*              | When Tasks are no longer needed, the Task Manager will        |
|                            | correctly clean up and destroy the service that was built to  |
|                            | handle the original Task.                                     |
+----------------------------+---------------------------------------------------------------+

## Task

A *Task* forms the core functionality of vehicle behavior. It is the point at which a vehicle
(or set of vehicles) is dedicated to a singular goal. During *Task* execution, a wide spectrum
of behavior is allowed, including updating waypoints and steering sensors. As part of the
core services, this general *Task* description stands in for all *Tasks* running in the system.

The general *Task* interaction with the rest of the task assignment pipeline is complex. It is
the aggregation of each *Task's* possibilities that defines the complexity of the overall
mission assignment. These *Task* possibilities are called *options* and they describe the
precise ways that a *Task* could unfold. For example, a *LineSearchTask* could present two
options to the system: 1) search the line from East-to-West and 2) search the line from
West-to-East. Either is valid and a selection of one of these options that optimizes overall
mission efficiency is the role of the assignment service.

A general *Task* is comprised of up to nine states with each state corresponding to a place
in the message sequence that carries out the task assignment pipeline. The states for a *Task*
are:

  - **Init**: This is the state that all *Tasks* start in and remain until all internal
initialization is complete. For example, a *Task* may need to load complex terrain or weather
data upon creation and will require some (possibly significant) start-up time. When a *Task*
has completed its internal initialization, it must report transition from this state via the
*TaskInitialized* message.
  - **Idle**: This represents the state of a *Task* after initialization, but before any
requests have been made that include the *Task*. *UniqueAutomationRequest* messages trigger
a transition from this state into the **SensorRequest** state.
  - **SensorRequest**: When a *Task* is notified of its inclusion (by noting the presence of
its ID in the *Tasks* list of an *UniqueAutomationRequest* message), it can request calculations
that pertain to the sensors onboard the vehicles that are also included in the
*UniqueAutomationRequest* message. While waiting for a response from the *SensorManagerService*,
a *Task* is in the **SensorRequest** state and will remain so until the response from the
*SensorManagerService* is received.
  - **OptionRoutes**: After the *SensorManagerService* has replied with the appropriate sensor
calculations, the *Task* can request waypoints from the *RouteAggregatorService* that carry
out the on-*Task* goals. For example, an *AreaSearchTask* can request routes from key
surveillance positions that ensure sensor coverage of the entire area. The *Task* remains in
the **OptionRoutes** state until the *RouteAggregatorService* replies.
  - **OptionsPublished**: When routes are returned to the *Task*, it will utilize
all route and sensor information to identify and publish the applicable *TaskOptions*. The
determination of *TaskOptions* is key to overall mission performance and vehicle behavior. It
is from this list of options that the assignment will select in order to perform this particular
*Task*. After publication of the options, a *Task* waits in the **OptionsPublished** state until
the *TaskImplementationRequest* message is received, whereupon it switches to **FinalRoutes**.
  - **FinalRoutes**: Upon reception of a *TaskImplementationRequest*, a *Task* is informed of
the option that was selected by the assignment service. At this point, a *Task* must create the
final set of waypoints that include both *enroute* and *on-task* waypoints from the specified
vehicle location. The *Task* is required to create the *enroute* waypoints since a
route refinement is possible, taking advantage of the concrete prior position of the selected
vehicle. The *Task* remains in the **FinalRoutes** state until the route request is fulfilled
by the *RouteAggregatorService*.
  - **OptionSelected**: When the final waypoints are returned from the *RouteAggregatorService*,
the *Task* publishes a complete *TaskImplementationResponse* message. A *Task* will remain in this
state until an *EntityState* message includes this *Task* ID in its *AssociatedTaskList*. If during
this state, a subsequent *UniqueAutomationRequest* is made, the *Task* returns to the
**SensorRequest** state and immediately attempts to fulfill the requirements of the new
*UniqueAutomationRequest*. This behavior implies that a *Task* can only be part of a single
*AutomationRequest* and subsequent requests always override previous requests.
  - **Active**: If the *Task* is in the **OptionSelected** state and an *EntityState* message is
received which includes the *Task* ID in the *AssociatedTaskList*, then the *Task* switches to the
**Active** state and is allowed to publish new waypoints and sensor commands at will. A *Task* remains
in the **Active** state until a subsequent *EntityState* message does *not* list the *Task* ID in
its *AssociatedTaskList*. At which point, a transition to **Completed** is made.
Note that a *Task* can reliquish control indirectly by sending the
vehicle to a waypoint not tagged with its own ID. Likewise, it can maintain control indefinitely
by ensuring that the vehicle only ever go to a waypoint that includes its ID. If a
*UniqueAutomationRequest* message that includes this *Task* ID is received in the **Active** state,
it transitions to the **Completed** state.
  - **Completed**: In this state, the *Task* publishes a *TaskComplete* message and then immediately
transitions to the **Idle** state.

: Table of messages that a general *Task* receives and processes.

+----------------------------+---------------------------------------------------------------+
| Message Subscription       | Description                                                   |
+============================+===============================================================+
| *UniqueAutomationRequest*  | Indicates which *Tasks* are to be considered as well as the   |
|                            | set of vehicles that can be used to fulfill those *Tasks*.    |
|                            | Upon reception of this message, if a *Task* ID is included,   |
|                            | it will publish *TaskPlanOptions*.                            |
+----------------------------+---------------------------------------------------------------+
|*TaskImplementationRequest* | After an assignment has been made, each *Task* involved is    |
|                            | requested to build the final set of waypoints that complete   |
|                            | the *Task* and corresponding selected option. A *Task* must   |
|                            | build the route **to** the *Task* as well as waypoints that   |
|                            | implement the *Task*. For each on-task waypoint, the          |
|                            | *AssociatedTaskList* must include the *Task* ID.              |
+----------------------------+---------------------------------------------------------------+
| *EntityConfiguration*      | Vehicle capabilities (e.g. allowable speeds) are described    |
|                            | by entity configuration messages. *Tasks* can reason over     |
|                            | sensor and vehicle capabilites to present the proper options  |
|                            | to other parts of the system. If a vehicle does not have the  |
|                            | capability to fulfill the *Task* (e.g. does not have a proper |
|                            | sensor), then the *Task* shall not include that vehicle ID in |
|                            | the list of eligible entities reported as part of an option.  |
+----------------------------+---------------------------------------------------------------+
| *EntityState*              | Describes the actual state of a vehicle in the system         |
|                            | including position, speed, and fuel status. This message is   |
|                            | primary feedback mechanism used for *Tasks* to switch to an   |
|                            | **Active** state. When a *Task* ID is listed in the           |
|                            | *AssociatedTaskList* of an *EntityState* message, the *Task*  |
|                            | is allowed to update waypoints and sensor commands at will.   |
+----------------------------+---------------------------------------------------------------+
| *RouteResponse*            | Collection of route plans that fulfill a set of requests for  |
|                            | navigation through an *OperatingRegion*. A *Task* must        |
|                            | request the waypoints to route a vehicle from its last        |
|                            | to the start of the *Task*. Additionally, this message        |
|                            | can be used to obtain on-task waypoints.                      |
+----------------------------+---------------------------------------------------------------+



: Table of messages that a general *Task* publishes.

+----------------------------+---------------------------------------------------------------+
| Message Publication        | Description                                                   |
+============================+===============================================================+
| *TaskPlanOptions*          | Primary message published by a *Task* to indicate the         |
|                            | potential different ways a *Task* could be completed. Each    |
|                            | possible way to fulfill a *Task* is listed as an *option*.    |
|                            | *TaskOptions* can also be related to each other via Process   |
|                            | Algebra.                                                      |
+----------------------------+---------------------------------------------------------------+
|*TaskImplementationResponse*| Primary message published by a *Task* that reports the final  |
|                            | set of waypoints to both navigate the selected vehicle to the |
|                            | *Task* as well as the waypoints necessary to complete the     |
|                            | *Task* using the selected option.                             |
+----------------------------+---------------------------------------------------------------+
| *RouteRequest*             | Collection of route plan requests to leverage the route       |
|                            | planner capability of constructing waypoints that adhere to   |
|                            | the designated *OperatingRegion*. This request is made for    |
|                            | waypoints en-route to the *Task* as well as on-task waypoints.|
+----------------------------+---------------------------------------------------------------+
| *VehicleActionCommand*     | When a *Task* is **Active**, it is allowed to update sensor   |
|                            | navigation commands to on-task vehicles. This message is used |
|                            | to directly command the vehicle to use the updated behaviors  |
|                            | calculated by the *Task*.                                     |
+----------------------------+---------------------------------------------------------------+
| *TaskComplete*             | Once a *Task* has met its goal or if a vehicle reports that   |
|                            | it is no longer on-task, a previously **Active** *Task* must  |
|                            | send a *TaskComplete* message to inform the system of this    |
|                            | change.                                                       |
+----------------------------+---------------------------------------------------------------+

## RoutePlannerVisibilityService

## RouteAggregatorService

## AssignmentTreeBranchBoundService

## PlanBuilderService

