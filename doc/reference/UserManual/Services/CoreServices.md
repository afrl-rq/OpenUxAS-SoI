
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

## RoutePlannerVisibilityService

## RouteAggregatorService

## AssignmentTreeBranchBoundService

## PlanBuilderService

