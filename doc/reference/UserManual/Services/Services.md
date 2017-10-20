Adding New Services: Step-By-Step
=================================

1.  Make copies of the service template source and header files:

    OpenUxAS/src/Services/00\_ServiceTemplate.cpp

    OpenUxAS/src/Services/00\_ServiceTemplate.h

2.  Change the name of the copied files to reflect the name of the new
    service.

3.  In the new files, search for the string *c00\_ServiceTemplate* and
    Replace it with the new service name.

4.  Change the unique include guard entries in the header file, i.e.
    *UXAS\_00\_SERVICE\_TEMPLATE\_H*, to match the new service name.

5.  Edit the file:

    OpenUxAS/src/Services/00\_ServiceList.h

    to add entries for the new service:

    1.  include the header file for the new service in the section
        labeled *SERVICE HEADER FILES SECTION*, e.g.:

        \#include “CmasiAreaSearchTaskService.h”

    2.  add a service registration string in the section labeled
        *SERVICE REGISTRATION SECTION* e.g.:

        [auto svc =
        uxas::stduxas::make\_unique&lt;afrl::cmasi::AreaSearchTask&gt;();]{}

    3.  if the new service is a task, include the header file of the
        corresponding task message in the section labeled *INCLUDE TASK
        MESSAGES SECTION*, e.g.:

        \#include “afrl/cmasi/AreaSearchTask.h”

    4.  if the new service is a task, add a subscription string in the
        section labeled *SUBSCRIBE TO TASKS SECTION*, e.g.:

        addSubscriptionAddress(afrl::cmasi::AreaSearchTask::AREASEARCHTASK\_FULL\_LMCP\_TYPE\_NAME);

* NOTE: Before recompiling OpenUxAS, the new service's file name should be added to the srcs_services array within the meson.build file. This file is located at OpenUxAS/src/services/meson.build

Configuring Services
====================

Service are configured using a global configuration file written in XML.
The configuration file is selected either by using the default
configuration file name: ***cfg.xml*** or passing in the path/filename
when starting UxAS:

uxas\_main **-cfgPath** *../PathToConfigurationFile/cfgFileName.xml*

The elements contained in an UxAS configuration file are, **XML
Declaration**, **UxAS Element**, **Service Elements**, and **Bridge
Elements**, see Figure \[fig:configExample\].

![image](\FiguresPath//ConfigExample){width="1.3\linewidth"}

Here is the **XML Declaration**:

&lt;?xml version=“1.0” encoding=“UTF-8” standalone=“yes” ?&gt;

The **UxAS Element**:

&lt;UxAS EntityID=“1000” FormatVersion=“1.0” EntityType=“Aircraft”&gt;

accepts the following attributes:

*EntityID*

:   Identification number of the entity represented by this instance of
    UxAS

*EntityType*

:   used to differentiate between entities such as, *Aircraft* and
    *UGS*. Entries are defined by the services that use them.

*ConsoleLoggerSeverityLevel*

:   if this attribute is present, all log messages at or below the
    severity level are displayed in the console. Valid entries are:
    *DEBUG*, *INFO*, *WARN*, and *ERROR*

*MainFileLoggerSeverityLevel*

:   if this attribute is present, all log messages at or below the
    severity level are save in log files. Valid entries are: *DEBUG*,
    *INFO*, *WARN*, and *ERROR*

*RunDuration\_s*

:   UxAS will run for *RunDuration\_s* seconds before terminating.

Service Elements configure the services. There can be as many Service
Elements as required. The attributes of the Service Elements are the
options defined by each service. For example, the HelloWorld service can
be configured with the following Service Element:

&lt;Service Type=“HelloWorld” StringToSend=“Hello from \#1”
SendPeriod\_ms=“1000”/&gt;

Bridge Elements configure bridges, which are services that create
communication connections. For the Distributed Cooperation example, the
zyre connection is configured with the following Bridge Element:

&lt;Bridge Type=“LmcpObjectNetworkZeroMqZyreBridge”
NetworkDevice=“enx281878b9065a”&gt; &lt;/Bridge&gt;

Core Services
=============

The core services of UxAS work in concert to carry out the *task
assignment pipeline* which automates the calculation of the proper
vehicle-task orderings for efficient overall mission completion. The
design choice to seperate each of these services is motivated by
consideration of computational complexity as well as availability in the
literature for parts of the process (i.e. route planners and task
assignment algorithms).

![image](\CCAFiguresPath//CCA_Components_MessageFLow){width="1.0\linewidth"}

The message flow between the core services is captured in
Figure \[fig:CoreServiceMessageFlow\] and indicates the temporal
relationship between the core services in carrying out a complete
automation request. Time proceeds from the top of the diagram to the
bottom with each horizontal arrow representing a single LMCP message of
the specified type.

***AutomationRequestValidatorService*** - This service will check an
outside automation request for feasibility. If any task, vehicle, or
operating region in the request has not yet been described to the
system, this service will return an error indicating that the request
cannot be fulfilled. If all necessary parts of the request are available
to the system, then this service will attach a unique identifier to the
request and start the sequence of steps necessary to fulfill that
request. If any other outside requests are made while the system is in
the process of fulfilling an existing request, this service will queue
those additional requests, ensuring that the system only handles one
request at a time.

***TaskManagerService*** - This service dynamically creates new task
services as their descriptions are sent into the system. When a new
*Task* is described, this service will send the proper configuration
message for construction of a new service that adheres to the general
task interface specification for that particular *Task*. As part of the
task service construction, this service will pass along all relevant
details that a *Task* needs for calculation of its behavior (i.e.
current vehicle states, defined areas of interest, etc).

***Task*** - Tasks make up the atomic building blocks of automation
requests. The composition of tasks and the assignment of particular
vehicles to tasks comprises an automation response. When included as
part of an automation request, a *Task* reports a set of possible
*options* which represent the possible ways that the task can be
completed. Each option is precisely a start and end location for
applicable vehicles as well as the cost to complete the task using that
option. The location and cost information for each option is used by the
assignment service to select an option for each task that completes the
overall mission efficiently. Once an option is selected by the
assignment service, each *Task* also reports the set of waypoints that a
vehicle should use to complete the task.

***RoutePlannerVisibilityService*** - One of potentially many route
planners, this service fulfills simple requests for routing in complex
environments. For a given environment (described by sets of *KeepIn* and
*KeepOut* polygons), a route planner will calculate the appropriate
waypoints to guide a vehicle from a prescribed start location to a
desired end location, ensuring that no waypoint is placed in an invalid
area. This particular route planner uses a visibility graph as a basis
to create distance-minimizing routes in two dimensions. Route planning
services have a simple request-reply interface with each request
corresponding to a single vehicle in a single environment.

***RouteAggregatorService*** - This service works with a set of route
planners, requesting routes from the appropriate planner based on the
situation. Additionally, this service provides the capability to make
large-scale route planning requests involving multiple vehicles and
multiple start/end locations. A primary use of this service is to
calculate routes for all vehicles to travel between task locations. By
orchestrating the cost-to-go calculations between tasks, this service
acts as the bookkeeper for the complete cost map required by assignment
algorithms.

***AssignmentTreeBranchBoundService*** - This service provides a
resource allocation algorithm to determine an efficient use of the
vehicle assets to fulfill tasks in the system. By design, the resource
allocation is de-coupled from route planning and only uses the costs
provided by the *RouteAggregatorService*. The ultimate output of this
service is an ordered list of tasks for each vehicle. This ordering must
account for the process algebra relationship between tasks. This
particular assignment service builds a tree of possible assignment
orderings and prunes that tree based on the prescribed task
relationships. The algorithm proceeds in two phases: 1) greedy,
depth-first search to find a feasible plan; 2) backtracking up the tree
in a branch-and-bound manner to discover plans that are lower cost than
the initial greedy plan. Once a predetermined amount of the tree has
been searched (to ensure worst-case execution time), the assignment
service will return the most efficient task ordering discovered.

***PlanBuilderService*** - With a task ordering determined by the
assignment service, the *PlanBuilderService* will organize the final set
of waypoints that each vehicle should follow to complete the assignment.
Working through the task ordering, this service requests the appropriate
*Tasks* in the assigned order to build a complete set of waypoints for
each vehicle to carry out the mission. By stitching each part of the
mission together in the proper order, this service provides the
automation response that fulfills the original, outside automation
request.

What follows are details for each of the core services and a rough
description of the state machines that each follows to complete its part
of the overall task assignment process. See the auto-generated LMCP
documentation for precise details of each message.

AutomationRequestValidatorService
---------------------------------

This service provides a simple sanity check on external automation
requests. It also queues requests and tags them with unique identifiers,
feeding them into the system one at a time.

This service has two states: **idle** and **busy**. In both states, when
a non *AutomationRequest* message is received, a local memory store is
updated to maintain a list of all available tasks, vehicle
configurations, vehicle states, zones, and operating regions.

Upon reception of an *AutomationRequest* message, this service ensures
that such a request can be carried out by checking its local memory
store for existence of the requested vehicles, tasks, and operating
region. If the request includes vehicles, tasks, or an operating region
that has not previously been defined, this service will publish an error
message.

Upon determination that the *AutomationRequest* includes only vehicles,
tasks, and an operating region that have previously been defined, this
service creates a *UniqueAutomationRequest* with a previously unused
unique identifier. If in the **idle** state, this service will
immediately publish the *UniqueAutomationRequest* message and transition
to the **busy** state. If already in the **busy** state, the
*UniqueAutomationRequest* will be added to the end of a queue.

When this service receives either an error message (indicating that the
*UniqueAutomationRequest* cannot be fulfilled or a corresponding
*UniqueAutomationResponse*), it will publish the same message. If in the
**idle** state, it will remain in the **idle** state. If in the **busy**
state, it will remove from the queue the request that was just fulfilled
and then send the next *UniqueAutomationRequest* in the queue. If the
queue is empty, this service transitions back to the **idle** state.

This service also includes a parameter that allows an optional *timeout*
value to be set. When a *UniqueAutomationRequest* is published, a timer
begins. If the *timeout* has been reached before a
*UniqueAutomationResponse* is received, an error is assumed to have
occured and this service removes the pending *UniqueAutomationRequest*
from the queue and attempts to send the next in the queue or transition
to **idle** if the queue is empty.



|  Message Subscription | Description |
|:---------------------:|:-------------------|
| *AutomationRequest* | Primary message to request a set of Tasks to be completed by a set of vehicles in a particular airspace configuration (described by an *OperatingRegion*). |
| (2 ms work) | Determines validity of *AutomationRequest*. **idle** -&gt; **busy**, emit *UniqueAutomationRequest* **busy** -&gt; **busy**, add *UniqueAutomationRequest* to queue |
| *EntityConfiguration* | Vehicle capabilities (e.g. allowable speeds) are described by entity configuration messages. Any vehicle requested in an *AutomationRequest* must previously be described by an associated *EntityConfiguration*. |
| (0 ms work) | Add to internal storage for use in validation step. **idle** -&gt; **idle**, add to storage **busy** -&gt; **busy**, add to storage |
| *EntityState* | Describes the actual state of a vehicle in the system including position, speed, and fuel status. Each vehicle in an *AutomationRequest* must have reported its state. |
| (0 ms work) | Add to internal storage for use in validation step. **idle** -&gt; **idle**, add to storage **busy** -&gt; **busy**, add to storage |
| *Task* | Details a particular task that will be referenced (by ID) in an *AutomationRequest*. |
| (0 ms work) | Add to internal storage for use in validation step. **idle** -&gt; **idle**, add to storage **busy** -&gt; **busy**, add to storage |
| *TaskInitialized* | Indicates that a particular task is ready to proceed with the task assignment sequence. Each task requested in the *AutomationRequest* must be initialized before a *UniqueAutomationRequest* is published. |
| (0 ms work) | Add to internal storage for use in validation step **idle** -&gt; **idle**, add to storage **busy** -&gt; **busy**, add to storage |
| *KeepOutZone* | Polygon description of a region in which vehicles must not travel. If referenced by the *OperatingRegion* in the *AutomationRequest*, zone must exist for request to be valid. |
| (0 ms work) | Add to internal storage for use in validation step. **idle** -&gt; **idle**, add to storage **busy** -&gt; **busy**, add to storage |
| *KeepInZone* | Polygon description of a region in which vehicles must remain during travel. If referenced by the *OperatingRegion* in the *AutomationRequest*, zone must exist for request to be valid. |
| (0 ms work) | Add to internal storage for use in validation step. **idle** -&gt; **idle**, add to storage **busy** -&gt; **busy**, add to storage |
| *OperatingRegion* | Collection of *KeepIn* and *KeepOut* zones that describe the allowable space for vehicular travel. Must be defined for *AutomationRequest* to be valid. |
| (0 ms work) | Add to internal storage for use in validation step. **idle** -&gt; **idle**, add to storage **busy** -&gt; **busy**, add to storage |
| *UniqueAutomationResponse* |   Completed response from the rest of the task assignment process. Indicates that the next *AutomationRequest* is ready to be processed. |
| (1 ms work) | If response ID does not match request ID at top of queue, ignore and remain in current state. Otherwise: **idle** -&gt; **idle**, normal operation should preclude receiving this message in the **idle** state **busy**, emit corresponding *AutomationResponse* If queue is empty, **busy** -&gt; **idle**, else **busy** -&gt; **busy**, emit request message at top of queue |

  : Table of messages that the *AutomationRequestValidatorService*
  receives and processes.

  |  Message Publication | Description |
  |:---------------------:|:-------------------|
| *UniqueAutomationRequest* |  A duplicate message to an external *AutomationRequest* but only published if the request is determined to be valid. Also includes a unique identifier to match to the corresponding response. |
|  *ServiceStatus* | Error message when a request is determined to be invalid. Includes human readable error message that highlights which portion of the *AutomationRequest* was invalid. |
| *AutomationResponse* |        Upon reception of a completed *UniqueAutomationResponse*, this message is published as a response to the original request. |

  : Table of messages that the *AutomationRequestValidatorService*
  publishes.

TaskManagerService
------------------

The *TaskManagerService* is a very straight-forward service. Upon
reception of a Task message, it will send the appropriate
*CreateNewService* message. To do so, it catalogues all entity
configurations and current states; areas, lines, and points of interest;
and current waypoint paths for each vehicle. This information is stored
in local memory and appended as part of the *CreateNewService* message
which allows new Tasks to immediately be informed of all relevant
information needed to carry out a Task.

When *TaskManagerService* receives a *RemoveTasks* message, it will form
the appropriate *KillService* message to properly destroy the service
that was created to fulfill the original Task.


| Message Subscription | Description |
|:--------------------:|:-----------|
| *Task* | Primary message that describes a particular task. The task manager will make the appropriate service creation message to build a service that directly handles this requested Task. |
| (1 ms work) | Emit *CreateNewService* message |
| *RemoveTasks* | Indicates that Task is no longer needed and will not be included in future *AutomationRequest* messages. Task manager will send the proper *KillService* message to remove the service that was constructed to handle the requested Task. |
| (1 ms work) | Emit *KillService* message corresponding to *Task* |
| *EntityConfiguration* | Vehicle capabilities (e.g. allowable speeds) are described by entity configuration messages. New Tasks are informed of all known entities upon creation. |
| (0 ms work) | Store to report during *Task* creation |
| *EntityState* | Describes the actual state of a vehicle in the system including position, speed, and fuel status. New Tasks are informed of all known entity states upon creation. |
| (0 ms work) | Store to report during *Task* creation |
| *AreaOfInterest* *LineOfInterest* *PointOfInterest* | Describes known geometries of areas, lines, and points. New Tasks are informed of all such named areas upon creation. |
| (0 ms work) | Store to report during *Task* creation |
| *MissionCommand* | Describes current set of waypoints that a vehicle is following. New Tasks are informed of all known current waypoint routes upon creation. |
| (0 ms work) | Store to report during *Task* creation |

  : Table of messages that the *TaskManagerService* receives and
  processes.

| Message Publication | Description |
| :---: | :---: |
| *CreateNewService* | Primary message published by the Task Manager to dynamically build a new Task from an outside description of such a Task. |
| *KillService* | When Tasks are no longer needed, the Task Manager will correctly clean up and destroy the service that was built to handle the original Task. |

  : Table of messages that the *TaskManagerService* publishes.

Task
----

A *Task* forms the core functionality of vehicle behavior. It is the
point at which a vehicle (or set of vehicles) is dedicated to a singular
goal. During *Task* execution, a wide spectrum of behavior is allowed,
including updating waypoints and steering sensors. As part of the core
services, this general *Task* description stands in for all *Tasks*
running in the system.

The general *Task* interaction with the rest of the task assignment
pipeline is complex. It is the aggregation of each *Task’s*
possibilities that defines the complexity of the overall mission
assignment. These *Task* possibilities are called *options* and they
describe the precise ways that a *Task* could unfold. For example, a
*LineSearchTask* could present two options to the system: 1) search the
line from East-to-West and 2) search the line from West-to-East. Either
is valid and a selection of one of these options that optimizes overall
mission efficiency is the role of the assignment service.

A general *Task* is comprised of up to nine states with each state
corresponding to a place in the message sequence that carries out the
task assignment pipeline. The states for a *Task* are:

-   **Init**: This is the state that all *Tasks* start in and remain
    until all internal initialization is complete. For example, a *Task*
    may need to load complex terrain or weather data upon creation and
    will require some (possibly significant) start-up time. When a
    *Task* has completed its internal initialization, it must report
    transition from this state via the *TaskInitialized* message.

-   **Idle**: This represents the state of a *Task* after
    initialization, but before any requests have been made that include
    the *Task*. *UniqueAutomationRequest* messages trigger a transition
    from this state into the **SensorRequest** state.

-   **SensorRequest**: When a *Task* is notified of its inclusion (by
    noting the presence of its ID in the *Tasks* list of an
    *UniqueAutomationRequest* message), it can request calculations that
    pertain to the sensors onboard the vehicles that are also included
    in the *UniqueAutomationRequest* message. While waiting for a
    response from the *SensorManagerService*, a *Task* is in the
    **SensorRequest** state and will remain so until the response from
    the *SensorManagerService* is received.

-   **OptionRoutes**: After the *SensorManagerService* has replied with
    the appropriate sensor calculations, the *Task* can request
    waypoints from the *RouteAggregatorService* that carry out the
    on-*Task* goals. For example, an *AreaSearchTask* can request routes
    from key surveillance positions that ensure sensor coverage of the
    entire area. The *Task* remains in the **OptionRoutes** state until
    the *RouteAggregatorService* replies.

-   **OptionsPublished**: When routes are returned to the *Task*, it
    will utilize all route and sensor information to identify and
    publish the applicable *TaskOptions*. The determination of
    *TaskOptions* is key to overall mission performance and vehicle
    behavior. It is from this list of options that the assignment will
    select in order to perform this particular *Task*. After publication
    of the options, a *Task* waits in the **OptionsPublished** state
    until the *TaskImplementationRequest* message is received, whereupon
    it switches to **FinalRoutes**.

-   **FinalRoutes**: Upon reception of a *TaskImplementationRequest*, a
    *Task* is informed of the option that was selected by the assignment
    service. At this point, a *Task* must create the final set of
    waypoints that include both *enroute* and *on-task* waypoints from
    the specified vehicle location. The *Task* is required to create the
    *enroute* waypoints since a route refinement is possible, taking
    advantage of the concrete prior position of the selected vehicle.
    The *Task* remains in the **FinalRoutes** state until the route
    request is fulfilled by the *RouteAggregatorService*.

-   **OptionSelected**: When the final waypoints are returned from the
    *RouteAggregatorService*, the *Task* publishes a complete
    *TaskImplementationResponse* message. A *Task* will remain in this
    state until an *EntityState* message includes this *Task* ID in its
    *AssociatedTaskList*. If during this state, a subsequent
    *UniqueAutomationRequest* is made, the *Task* returns to the
    **SensorRequest** state and immediately attempts to fulfill the
    requirements of the new *UniqueAutomationRequest*. This behavior
    implies that a *Task* can only be part of a single
    *AutomationRequest* and subsequent requests always override previous
    requests.

-   **Active**: If the *Task* is in the **OptionSelected** state and an
    *EntityState* message is received which includes the *Task* ID in
    the *AssociatedTaskList*, then the *Task* switches to the **Active**
    state and is allowed to publish new waypoints and sensor commands at
    will. A *Task* remains in the **Active** state until a subsequent
    *EntityState* message does *not* list the *Task* ID in its
    *AssociatedTaskList*. At which point, a transition to **Completed**
    is made. Note that a *Task* can reliquish control indirectly by
    sending the vehicle to a waypoint not tagged with its own ID.
    Likewise, it can maintain control indefinitely by ensuring that the
    vehicle only ever go to a waypoint that includes its ID. If a
    *UniqueAutomationRequest* message that includes this *Task* ID is
    received in the **Active** state, it transitions to the
    **Completed** state.

-   **Completed**: In this state, the *Task* publishes a *TaskComplete*
    message and then immediately transitions to the **Idle** state.

| Message Subscription | Description |
|:---:|:---|
| *UniqueAutomationRequest* | Indicates which *Tasks* are to be considered as well as the set of vehicles that can be used to fulfill those *Tasks*. Upon reception of this message, if a *Task* ID is included, it will publish *TaskPlanOptions*. |
| (2 ms work) | If included in the request, begin process of calculating task options and costs by emitting *SensorFootprintRequests* **Idle** -&gt; **SensorRequest** in normal operation **OptionSelected** -&gt; **SensorRequest**, when interrupted |
| *TaskImplementationRequest* | After an assignment has been made, each *Task* involved is requested to build the final set of waypoints that complete the *Task* and corresponding selected option. A *Task* must build the route **to** the *Task* as well as waypoints that implement the *Task*. For each on-task waypoint, the *AssociatedTaskList* must include the *Task* ID. |
| (2 ms work) | **OptionsPublished** -&gt; **FinalRoutes**, emit *RouteRequest* to determine final waypoint routes needed for implementation |
| *EntityConfiguration* | Vehicle capabilities (e.g. allowable speeds) are described by entity configuration messages. *Tasks* can reason over sensor and vehicle capabilites to present the proper options to other parts of the system. If a vehicle does not have the capability to fulfill the *Task* (e.g. does not have a proper sensor), then the *Task* shall not include that vehicle ID in the list of eligible entities reported as part of an option. |
| (0 ms work) | Add to internal storage for use in calculating options No state change |
| *EntityState* | Describes the actual state of a vehicle in the system including position, speed, and fuel status. This message is primary feedback mechanism used for *Tasks* to switch to an **Active** state. When a *Task* ID is listed in the *AssociatedTaskList* of an *EntityState* message, the *Task* is allowed to update waypoints and sensor commands at will. |
| (0 ms work) | **OptionSelected**: if *Task* ID is listed in *AssociatedTaskList*, then -&gt; **Active** **Active**: if *Task* ID is NOT listed in *AssociatedTaskList*, then -&gt; **Completed** |
| *RouteResponse* | Collection of route plans that fulfill a set of requests for navigation through an *OperatingRegion*. A *Task* must request the waypoints to route a vehicle from its last to the start of the *Task*. Additionally, this message can be used to obtain on-task waypoints. |
| (1 ms work) | **OptionRoutes** -&gt; **OptionsPublished**, emit *TaskPlanOptions* **FinalRoutes** -&gt; **OptionSelected**, emit *TaskImplementationResponse* |
| *SensorFootprintResponse* | Collection of sensor information at different conditions corresponding to a *SensorFootprintRequests* message. Used to determine if a particular entity with known sensor payloads can meet the sensor resolution constraints required to fulfill this *Task*. |
| (1 ms work) | **SensorRequest** -&gt; **OptionRoutes**, emit *RouteRequest* to determine on-*Task* waypoints |

  : Table of messages that a general *Task* receives and processes.

| Message Publication | Description|
|:---:|:---|
| *TaskPlanOptions* | Primary message published by a *Task* to indicate the potential different ways a *Task* could be completed. Each possible way to fulfill a *Task* is listed as an *option*. *TaskOptions* can also be related to each other via Process Algebra. |
| *TaskImplementationResponse* | Primary message published by a *Task* that reports the final set of waypoints to both navigate the selected vehicle to the *Task* as well as the waypoints necessary to complete the *Task* using the selected option. |
| *RouteRequest* | Collection of route plan requests to leverage the route planner capability of constructing waypoints that adhere to the designated *OperatingRegion*. This request is made for waypoints en-route to the *Task* as well as on-task waypoints. |
| *SensorFootprintRequests* | Collection of requests to the *SensorManagerService* to determine ground-sample distances possible for each potential entity. Uses camera and gimbal information from the cached *EntityConfiguration* messages. |
| *VehicleActionCommand* | When a *Task* is **Active**, it is allowed to update sensor navigation commands to on-task vehicles. This message is used to directly command the vehicle to use the updated behaviors calculated by the *Task*. |
| *TaskComplete* | Once a *Task* has met its goal or if a vehicle reports that it is no longer on-task, a previously **Active** *Task* must send a *TaskComplete* message to inform the system of this change. |

  : Table of messages that a general *Task* publishes.

RoutePlannerVisibilityService
-----------------------------

The *RoutePlannerVisibilityService* is a service that provides route
planning using a visibility heuristic. One of the fundamental
architectural decisions in UxAS is separation of route planning from
task assignment. This service is an example of a route planning service
for aircraft. Ground vehicle route planning (based on Open Street Maps
data) can be found in the *OsmPlannerService*.

The design of the *RoutePlannerVisibilityService* message interface is
intended to be as simple as possible: a route planning service considers
routes only in fixed environments for known vehicles and handles
requests for single vehicles. The logic necessary to plan for multiple
(possibly heterogeneous) vehicles is handled in the
*RouteAggregatorService*.

In two dimensional environments composed of polygons, the shortest
distance between points lies on the visibility graph. The
*RoutePlannerVisibilityService* creates such a graph and, upon request,
adds desired start/end locations to quickly approximate a
distance-optimal route through the environment. With the straight-line
route created by the searching the visibility graph, a smoothing
operation is applied to ensure that minimum turn rate constraints of
vehicles are satisfied. Note, this smoothing operation can violate the
prescribed keep-out zones and is not guaranteed to smooth arbitrary
straight-line routes (in particular, path segments shorter than the
minimum turn radius can be problematic).

Due to the need to search over many possible orderings of *Tasks* during
an assignment calculation, the route planner must very quickly compute
routes. Even for small problems, hundreds of routes must be calculated
before the assignment algorithm can start searching over the possible
ordering. For this reason it is imperative that the route planner be
responsive and efficient.

  | Message Subscription | Description |
  |:---:|:---|
  | *RoutePlanRequest* “AircraftPathPlanner” | Primary message that describes a route plan request. A request considers only a single vehicle in a single *OperatingRegion* although it can request multiple pairs of start and end locations with a single message. In addition to subscribing to *RoutePlanRequest*, this service also subscribes to the group mailbox “AircraftPathPlanner”. Upon reception of a message on this channel, the service will process it as if it came over the broadcast channel. The return message always uses return-to-sender addressing. |
| (10 ms work) | For each start/end pair, this service will compute a path that respects the geometric constraints imposed by the corresponding *OperatingRegion*. For each start/end pair, the route planner could reasonably work for 10ms to complete the calculation. Once all have been calculated, emits *RoutePlanResponse*. |
| *KeepOutZone* | Polygon description of a region in which vehicles must not travel. This service will track all *KeepOutZones* to compose them upon reception of an *OperatingRegion*. |
| (0 ms work) | Store for use during calculation of operating region map |
| *KeepInZone* | Polygon description of a region in which vehicles must remain during travel. This service will track all *KeepInZones* to compose them upon reception of an *OperatingRegion*. |
| (0 ms work) | Store for use during calculation of operating region map |
| *OperatingRegion* | Collection of *KeepIn* and *KeepOut* zones that describe the allowable space for vehicular travel. When received, this service creates a visibility graph considering the zones referenced by this *OperatingRegion*. Upon *RoutePlanRequest* the visibility graph corresponding to the *OperatingRegion* ID is retreived and manipulated to add start/end locations and perform the shortest path search. |
| (20 ms work) | To respond quickly to *RoutePlanRequest* messages, the *RoutePlannerVisibilityService* will create a pre-processed map using the geometric constraints from the *OperatingRegion*. The result is stored for later requests. |
| *EntityConfiguration* | Vehicle capabilities (e.g. allowable speeds) are described by entity configuration messages. This service calculates the minimum turn radius of the entity by using the max bank angle and nominal speed. Requested routes are then returned at the nominal speed and with turns approximating the minimum turn radius. |
| (20 ms work) | Stored for use during *RoutePlanRequest*s. Also used to update operating region maps based on the capability of the entity. |

  : Table of messages that the *RoutePlannerVisibilityService* receives
  and processes.

| Message Publication | Description |
|:---|:---|
| *RoutePlanResponse* | This message contains the waypoints and time cost that fulfills the route request. This message is the only one published by the *RoutePlannerVisibilityService* and is always sent using the return-to-sender addressing which ensures that only the original requester receives the response. |

  : Table of messages that the *RoutePlannerVisibilityService*
  publishes.

RouteAggregatorService
----------------------

The *RouteAggregatorService* fills two primary roles: 1) it acts as a
helper service to make route requests for large numbers of heterogenous
vehicles; and 2) it constructs the task-to-task route-cost table that is
used by the assignment service to order the tasks as efficiently as
possible. Each functional role acts independently and can be modeled as
two different state machines.

The *Aggregator* role orchestrates large numbers of route requests
(possibly to multiple route planners). This allows other services in the
system (such as *Tasks*) to make a single request for routes and receive
a single reply with the complete set of routes for numerous vehicles.

For every aggregate route request (specified by a *RouteRequest*
message), the *Aggregator* makes a series of *RoutePlanRequests* to the
appropriate route planners (i.e. sending route plan requests for ground
vehicles to the ground vehicle planner and route plan requests for
aircraft to the aircraft planner). Each request is marked with a request
ID and a list of all request IDs that must have matching replies is
created. The *Aggregator* then enters a **pending** state in which all
received plan replies are stored and then checked off the list of
expected replies. When all of the expected replies have been received,
the *Aggregator* publishes the completed *RouteResponse* and returns to
the **idle** state.

Note that every aggregate route request corresponds to a separate
internal checklist of expected responses that will fulfill the original
aggregate request. The *Aggregator* is designed to service each
aggregate route request even if a previous one is in the process of
being fulfilled. When the *Aggregator* receives any response from a
route planner, it checks each of the many checklists to determine if all
expected responses for a particuarl list have been met. In this way, the
*Aggregator* is in a different **pending** state for each aggregate
request made to it.

| Message Subscription | Description |
|:---:|:---|
| *RouteRequest* | Primary message that requests a large number of routes for potentially heterogeneous vehicles. The *Aggregator* will make a series of *RoutePlanRequests* to the appropriate planners to fulfill this request. |
| (1 ms work) | **idle** -&gt; **pending**, indexed by *RouteRequest* request ID, create a checklist of expected responses. Emit a number of *RoutePlanRequest* messages equal to the number of vehicles in the `VehicleID` field of the original *RouteRequest* |
| *EntityConfiguration* | Vehicle capabilities (e.g. allowable speeds) are described by entity configuration messages. This service uses the *EntityConfiguration* to determine which type of vehicle corresponds to a specific ID so that ground planners are used for ground vehicles and air planners are used for aircraft. |
| (0 ms work) | No state change. Store to identify appropriate route planner by vehicle ID. |
| *RoutePlanResponse* | This message is the fulfillment of a single vehicle route plan request which the *Aggregator* catalogues until the complete set of expected responses is received. |
| (1 ms work) | Store response and check to see if this message completes any checklist. If a checklist is complete, use the corresponding request ID to create a complete *RouteResponse* message. Emit *RouteResponse* and **pending** -&gt; **idle**. |

  : Table of messages that the *RouteAggregatorService* receives and
  processes in its *Aggregator* role.

| Message Publication | Description |
|:---:|:---|
| *RouteResponse* | Once the *Aggregator* has a complete set of responses collected from the route planners, the message is built as a reply to the original *RouteRequest*. |
| *RoutePlanRequest*| The *Aggregator* publishes a series of these requests in order to fulfill an aggregate route request. These messages are published in batch, without waiting for a reply. It is expected that eventually all requests made will be fulfilled. |

  : Table of messages that the *RouteAggregatorService* publishes in its
  *Aggregator* role.

The *RouteAggregatorService* also acts in the role of creating the
*AssignmentCostMatrix* which is a key input to the assignment service.
For simplicity, this role will be labeled as the *Collector* role. This
role is triggered by the *UniqueAutomationRequest* message and begins
the process of collecting a complete set of on-task and between-task
costs.

The *Collector* starts in the **Idle** state and upon reception of a
*UniqueAutomationRequest* message, it creates a list of *Task* IDs that
are involved in the request and then moves to the **OptionsWait** state.
In this state, the *Collector* stores all *TaskPlanOptions* and matches
them to the IDs of the *Task* IDs that were requested in the
*UniqueAutomationRequest*. When the expected list of *Tasks* is
associated with a corresponding *TaskPlanOptions*, the *Collector* moves
to the **RoutePending** state. In this state, the *Collector* makes a
series of route plan requests from 1) initial conditions of all vehicles
to all tasks and 2) route plans between the end of each *Task* and start
of all other *Tasks*. Similar to the *Aggregator*, the *Collector*
creates a checklist of expected route plan responses and uses that
checklist to determine when the complete set of routes has been returned
from the route planners. The *Collector* remains in the **RoutePending**
state until all route requests have been fulfilled, at which point it
collates the responses into a complete *AssignmentCostMatrix*. The
*AssignmentCostMatrix* message is published and the *Collector* returns
to the **Idle** state.

Note that the *AutomationValidatorService* ensures that only a single
*UniqueAutomationRequest* is handled by the system at a time. However,
the design of the *Collector* does allow for multiple simultaneous
requests as all checklists (for pending route and task option messages)
are associated with the unique ID from each *UniqueAutomationRequest*.

| Message Subscription | Description |
|:---:|:---|
| *UniqueAutomationRequest* | Primary message that initiates the collection of options sent from each *Task* via the *TaskPlanOptions* message. A list of all *Tasks* included in the *UniqueAutomationRequest* is made upon reception of this message and later used to ensure that all included *Tasks* have responded. |
| (1 ms work) | **Idle** -&gt; **OptionsWait**, create checklist of expected task options. |
| *TaskPlanOptions* | Primary message from *Tasks* that prescribe available start and end locations for each option as well as cost to complete the option. Once all expected *TaskPlanOptions* have been received, the *Collector* will use the current locations of the vehicles to request paths from each vehicle to each task option and from each task option to every other task option. |
| (1 ms work) | Store task options and check to see if this message completes the checklist. If the checklist is complete, create a series of *RoutePlanRequest* messages to find routes from the current locations of vehicles to each task and from each task to every other task. Emit this series of *RoutePlanRequest* messages, **OptionsWait** -&gt; **RoutePending**. |
| *EntityState* | Describes the actual state of a vehicle in the system including position, speed, and fuel status. This message is used to create routes and cost estimates from the associated vehicle position and heading to the task option start locations. |
| (0 ms work) | No state change. Store for use in requesting routes from vehicle positions to task start locations. |
| *RoutePlanResponse* | This message is the fulfillment of a single vehicle route plan request which the *Collector* catalogues until the complete set of expected responses is received. |
| (1 ms work) | Store response and check to see if this message completes the cost matrix. If so, emit *AssignmentCostMatrix* and **RoutePending** -&gt; **Idle**. |

  : Table of messages that the *RouteAggregatorService* receives and
  processes in its *Collector* role.

| Message Publication | Description |
|:---:|:---|
| *AssignmentCostMatrix* | Once the *Collector* has a complete set of *TaskPlanOptions* as well as routes between tasks and vehicles, this message is built to inform the next step in the task assignment pipeline: the *AssignmentTreeBranchBoundService*. |
| *RoutePlanRequest* | The *Collector* publishes a series of these requests in order to compute the vehicle-to-task and task-to-task route costs. These messages are published in batch, without waiting for a reply. It is expected that eventually all requests made will be fulfilled. |

  : Table of messages that the *RouteAggregatorService* publishes in its
  *Collector* role.

AssignmentTreeBranchBoundService
--------------------------------

The *AssignmentTreeBranchBoundService* is a service that does the
primary computation to determine an efficient ordering and assignment of
all *Tasks* to the available vehicles. The assignment algorithm reasons
only at the cost level; in other words, the assignment itself does not
directly consider vehicle motion but rather it uses estimates of that
motion cost. The cost estimates are provided by the *Tasks* (for on-task
costs) and by the *RouteAggregatorService* for task-to-task travel
costs.

The *AssignmentTreeBranchBoundService* can be configured to optimize
based on cumulative team cost (i.e. sum total of time required from each
vehicle) or the maximium time of final task completion (i.e. only the
final time of total mission completion is minimized). For either
optimization type, this service will first find a feasible solution by
executing a depth-first, greedy search. Although it is possible to
request a mission for which **no** feasible solution exists, the vast
majority of missions are underconstrained and have an exponential
(relative to numbers of vehicles and tasks) number of solutions from
which an efficient one must be discovered.

After the *AssignmentTreeBranchBoundService* obtains a greedy solution
to the assignment problem, it will continue to search the space of
possibilities via backtracking up the tree of possibilities and
*branching* at descision points. The cost of the greedy solution acts as
a *bound* beyond which no solution is be considered. In other words, as
more efficient solutions are discovered, any partial solution that
exeeds the cost of the current best solution will immediately be
abandoned (cut) to focus search effort in the part of the space that
could possibly lead to better solutions. In this way, solution search
progresses until all possibilities have been exhausted or a
pre-determined tree size has been searched. By placing an upper limit on
the size of the tree to search, worst-case bounds on computation time
can be made to ensure desired responsiveness from the
*AssignmentTreeBranchBoundService*.

General assignment problems do not normally allow for specification of
*Task* relationships. However, the *AssignmentTreeBranchBoundService*
relies on the ability to specify *Task* relationships via Process
Algebra constraints. This enables creation of moderately complex
missions from simple atomic *Tasks*. Adherence to Process Algebra
constraints also allows *Tasks* to describe their *option*
relationships. The Process Algebra relationships of a particular *Task*
option are directly substituted into and replace the original *Task* in
the mission-level Process Algebra specification. Due to the heavy
reliance on Process Algebra specifications, any assignment service that
replaces *AssignmentTreeBranchBoundService* must also guarantee
satisfaction of such specifications.

The behavior of the *AssignmentTreeBranchBoundService* is
straight-foward. Upon reception of a *UniqueAutomationRequest*, this
service enters the **wait** state and remains in this state until a
complete set of *TaskPlanOptions* and an *AssignmentCostMatrix* message
have been received. In the **wait** state, a running list of the
expected *TaskPlanOptions* is maintained and checked off when received.
Upon receiving the *AssignmentCostMatrix* (which should be received
strictly after the *TaskPlanOptions* due to the behavior of the
*RouteAggregatorService*), this service conducts the branch-and-bound
search to determine the proper ordering and assignment of *Tasks* to
vehicles. The results of the optimization are packaged into the
*TaskAssignmentSummary* and published, at which point this service
returns to the **idle** state.

| Message Subscription | Description |
|:---:|:---|
| *UniqueAutomationRequest* | Sentinel message that initiates the collection of options sent from each *Task* via the *TaskPlanOptions* message. A list of all *Tasks* included in the *UniqueAutomationRequest* is made upon reception of this message and later used to ensure that all included *Tasks* have responded. |
| (0 ms work) | **idle** -&gt; **wait**, store request ID for identification of corresponding *TaskPlanOptions* and *AssignmentCostMatrix*. |
| *TaskPlanOptions* | Primary message from *Tasks* that prescribe available start and end locations for each option as well as cost to complete the option. In the **wait** state, this service will store all reported options for use in calculating mission cost for vehicles when considering possible assignments. |
| (0 ms work) | No state change. Store cost of each task option for look-up during optimization. |
| *AssignmentCostMatrix* | Primary message that initiates the task assignment optimization. This message contains the task-to-task routing cost estimates and is a key factor in determining which vehicle could most efficiently reach a *Task*. Coupled with the on-task costs captured in the *TaskPlanOptions*, a complete reasoning over both traveling to and completing a *Task* can be looked up during the search over possible *Task* orderings. |
| (1500 ms work) | Using the cost of each task option (from the stored *TaskPlanOptions* messages) and the cost for each vehicle to reach each option (from *AssignmentCostMatrix*), perform an optimization attempting to find the minimal cost mission that adheres to the Process Algebra contraints. Upon completion, emit *TaskAssignmentSummary* and **wait** -&gt; **idle**. |

  : Table of messages that the *AssignmentTreeBranchBoundService*
  receives and processes.

| Message Publication | Description |
|:---:|:---|
| *TaskAssignmentSummary* | The singular message published by this service which precisely describes the proper ordering of *Tasks* and the vehicles that are assigned to complete each *Task*. |

: Table of messages that the *AssignmentTreeBranchBoundService*
  publishes.

PlanBuilderService
------------------

The final step in the task assignment pipeline is converting the
decisions made by the *AssignmentTreeBranchBoundService* into waypoint
paths that can be sent to each of the vehicles. Using the ordering of
*Tasks* and the assigned vehicle(s) for each *Task*, the
*PlanBuilderService* will query each *Task* in turn to construct enroute
and on-task waypoints to complete the mission.

Similar to both the *RouteAggregator* and the
*AssignmentTreeBranchBoundService*, the *PlanBuilderService* utilizes a
received *UniqueAutomationRequest* to detect that a new mission request
has been made to the system. The *UniqueAutomationRequest* is stored
until a *TaskAssignmentSummary* that corresponds to the unique ID is
received. At this point, the *PlanBuilderService* transitions from the
**idle** state to the **busy** state.

Using the list of ordered *Tasks* dictated by the
*TaskAssignmentSummary*, the *PlanBuilderService* sends a
*TaskImplementationRequest* to each *Task* in order and waits for a
*TaskImplementationResponse* from each *Task* before moving to the next.
This is necessary as the ending location of a previous *Task* becomes
the starting location for a subsequent *Task*. Since each *Task* is
allowed to refine its final waypoint plan at this stage, the exact
ending location may be different that was was originally indicated
during the *TaskPlanOptions* phase. By working through the *Task* list
in assignment order, all uncertainty about timing and location is
elminated and each *Task* is allowed to make a final determination on
the waypoints to be used.

Once all *Tasks* have reponded with a *TaskImplementationResponse*, the
*PlanBuilderService* links all waypoints for each vehicle into a
complete *MissionCommand*. The total set of *MissionCommands* are
collected into the *UniqueAutomationResponse* which is broadcast to the
system and represents a complete solution to the original
*AutomationRequest*. At this point, the *PlanBuilderService* returns to
the **idle** state.


| Message Subscription| Description|
|:---:|:---|
| *TaskAssignmentSummary* | Primary message that dictates the proper order and vehicle assignment to efficiently carry out the requested mission. Upon reception of this messsage, the *PlanBuilderService* queries each *Task* in order for the final waypoint paths. |
| (2 ms work) | **idle** -&gt; **busy**, create a queue of ordered *TaskImplementationRequest* messages in the order prescribed by the *TaskAssignmentSummary*. Emit request at top of queue. |
| *EntityState* | Describes the actual state of a vehicle in the system including position, speed, and fuel status. This message is used to inform the first *Task* of the location of the vehicles. Subsequent *Tasks* use the predicted positions and headings of vehicles after previous *Tasks* have reported waypoints earlier in the mission. |
| (0 ms work) | No state change. Store for use in creating *TaskImplementationRequest* messages. |
| *TaskImplementationResponse* | Primary message that each *Task* reports to inform this service of the precise waypoints that need to be followed to reach the *Task* and carry it out correctly. The ordered collection of these messages are used to build the final *UniqueAutomationResponse*. |
| (2 ms work) | Remove top of task request queue and update predicted locations of vehicles. If task request queue is not empty, configure request at top of queue with predicted vehicle positions and emit the corresponding *TaskImplementationRequest* message. If queue is empty, **busy** -&gt; **idle**. |
| *UniqueAutomationRequest* | Informs this service of a new mission request in the system. Contains the desired starting locations and headings of the vehicles that are to be considered as part of the solution. |
| (0 ms work) | No state change. Store for use in creating *TaskImplementationRequest* messages. Note, positions in *UniqueAutomationRequest* override reported state positions stored when *EntityState* messages are received. |

  : Table of messages that the *PlanBuilderService* receives and
  processes.

| Message Publication | Description |
|:---:|:---|
| *TaskImplementationRequest* | The primary message used to query each *Task* for the proper waypoints that both reach and carry out the *Task*. Once the *PlanBuilderService* receives a corresponding response from each *Task*, it can construct a final set of waypoints for each vehicle. |
| *UniqueAutomationResponse* | This message contains a list of waypoints for each vehicle that was considered during the automation request. This collection of complete waypoints for the team fulfills the original request. |

  : Table of messages that the *PlanBuilderService* publishes.

Additional Services
===================

***SensorManagerService*** - A service that constructs sensor
footprints, calculates GSDs, determine sensor settings.

***WaypointPlanManagerService*** - Serves waypoint plans to the vehicle
interface.

***00\_ServiceTemplate*** - This is a basic service that can be used as a template when
constructing new services.

***01\_HelloWorld*** - This is a basic example of a UxAS service that sends/receives
KeyValuePair messages and prints out the results.

***BatchSummaryService*** -

***MessageLoggerDataService*** - This service logs messages received from other UxAS services to a
SQLite database. Logging can be configured to log either all or a subset
of service messages.

***OperatingRegionStateService*** -

***OsmPlannerService***- loads an Open Street Map file and constructs ground plans/costs to be
used for assignments.

***SendMessageService*** - sends out messages, loaded from files, at a given time or
periodically.

***ServiceBase*** - the base class for all UxAS service classes. Service class
constructors are registered in the *ServiceBase* creation registry.

***ServiceManager*** - a singleton class that inherits from the *ServiceBase* class. It
performs initial service creation for the UxAS entity at startup. After
entity startup, it creates services per requests received from other
services via messaging. The ServiceManager exclusively uses the
*ServiceBase* creation registry to create services.

Task Services
=============

***00\_TaskTemplate***   - This is a basic task that can be used as a template when
    constructing new tasks

***AngledAreaSearchTaskService***   - Area search task with specified direction

***BlockadeTaskService***   - Task for using multiple vehicles to surround an entity, for
    example, multiple surface vehicles surrounding incoming enemy ship.

***CmasiAreaSearchTaskService***   - Area search task

***CmasiLineSearchTaskService***   - Defines a line search task. A line search is a list of points that forms a polyline. The ViewAngleList determines from which direction the line may be viewed. View angles are specified using the Wedge type. If the UseInertialViewAngles option is true, then wedges are defined in terms of North-East coordinates, otherwise wedges are defined relative to the line segment currently being viewed (a vector from point i through point i+1). To be a valid look angle, the line segment must be viewed from an angle within the bounds of the wedge.

***CmasiPointSearchTaskService***   - Point search task

***CommRelayTaskService***   - Task for providing comm relay support

***CordonTaskService***   - Task for using multiple ground vehicles to block access to an area. Given a point to secure and a standoff distance, task identifies number (K) routes that must be blocked to successfully deny access to the area. If there are not enough eligible vehicles, then this task will use the maximum number of eligible vehicles in a best effort strategy which attempts to maximize radial coverage.

***EscortTaskService***   - Task for targeting surveillance at an offset of a moving entity, for example to scout ahead of a convoy.

***ImpactLineSearchTaskService***   - Defines a line search task. A line search is a list of points that forms a polyline. The ViewAngleList determines from which direction the line may be viewed. View angles are specified using the Wedge type. If the UseInertialViewAngles option is true, then wedges are defined in terms of North-East coordinates, otherwise wedges are defined relative to the line segment currently being viewed (a vector from point i through point i+1). To be a valid look angle, the line segment must be viewed from an angle within the bounds of the wedge.

***ImpactPointSearchTaskService***   - Impact Point Search Task

***OverwatchTaskService***   - Multi vehicle overwatch task

***PatternSearchTaskService***   - Search task with specified search pattern

***TaskManagerService***   - A service that constructs/destroys tasks.

***TaskServiceBase***   - A base service that implements storage/functions common to all
    tasks.

Connection Services
===================

***LmcpObjectNetworkPublishPullBridge***   -

***LmcpObjectNetworkSerialBridge***   -

***LmcpObjectNetworkSubscribePushBridge***   - connects an external entity to the internal message bus using
    *ZMQ\_SUB* and *ZMQ\_PUSH* sockets.

***LmcpObjectNetworkTcpBridge***   - connects an external TCP/IP stream to the internal message bus.

***LmcpObjectNetworkZeroMqZyreBridge***   - provides network discovery and communications. Dynamically discovers and bridges with zero-many Zyre-enabled systems.

***ZeroMqZyreBridge***   - provides network discovery and communications. Dynamically discovers and bridges with zero-many Zyre-enabled systems.

Logging and Data Capture Services
=================================

***MessageLoggerDataService***  - logs messages received from other UxAS services to files in a directory. Logging can be configured to log either all or a subset of service messages.
