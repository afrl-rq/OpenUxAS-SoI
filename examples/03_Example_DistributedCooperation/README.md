# Distributed Cooperation Example

This is an example of running UxAS services that communicate with each other to synchronize plannning and assignment of vehicles to tasks. The copies of UxAS exchange 'AssignmentCoordination' messages which contain the vehicle positions and headings that each vehicle will use for planning and assignment. Since the copies of UxAS are running the same assignment software, synchronizing the inputs will also syncronize the outputs. Each copy of UxAS runs the assignment algorithm for all known vehicles and implements the assignments corresponding to its own ID, this is using a "centralized" algorithm in a "decentralized" implementation.

## Files:

* `cfgDistributedCooperation_1000.xml` - UxAS configuration file for vehicle 1000
* `cfgDistributedCooperation_2000.xml` - UxAS configuration file for vehicle 2000
* `runUxAS_DistributedCooperation.sh` - bash script to run the example
* 
## The 'MessagesToSend' directory contains files with xml encoded LMCP messages that are sent in to UxAS using the 'MessagesToSend' service. ##

* `MessagesToSend/AirVehicleConfiguration_V????.xml` - the air vehicle configurations for vehicles 1000, 2000, and 3000.
* `MessagesToSend/AirVehicleState_V????.xml` - initial air vehicle states for vehicles  1000 and 2000.
* `MessagesToSend/AngledAreaSearchTask_51.xml` - an IMPACT angled area search task.
* `MessagesToSend/AreaOfInterest_100.xml` - the area that AngledAreaSearchTask_51 will search.
* `MessagesToSend/AreaSearchTask_50.xml` - a CMASI area search task.
* `MessagesToSend/AssignmentCoordinatorTask.xml` - the task that coordinates vehicle states before the assignment
* `MessagesToSend/CoordinatedAutomationRequest.xml` - the automation request used in conjunction with the AssignmentCoordinatorTask
* `MessagesToSend/ImpactLineSearchTask_21.xml` - an IMPACT line search task.
* `MessagesToSend/KeepOutZone_??.xml` - polygons that represent areas that the vehicle are not to enter.
* `MessagesToSend/LineOfInterest_101.xml` - points of the line for ImpactLineSearchTask_21.
* `MessagesToSend/LineSearchTask_??.xml` - a CMASI line search task.
* `MessagesToSend/OperatingRegion_100.xml` - the operating region, i.e. set of keep-in and keep-out tasks, to be used in the assignment.



## Running the Example:
1. open a ternimal window in the directory: "examples/03_Example_DistributedCooperation/"
2. enter the command: `./runUxAS_DistributedCooperation.sh`


### What Happens?
* Two console windows will open, each will have UxAS running.
## FOR EACH COPY OF UxAS ##
* By the end of the first second, all air vehicle configurations and states, as well as all tasks and associated messages are sent in to UxAS using the 'SendMessages' service.
* Each 'LmcpObjectNetworkZeroMqZyreBridge' will make a connection with the other copy of UxAS.
* At two seconds an air vehicle state, corresponding to the entity ID, is sent to UxAS. This state must be sent to UxAS after the assignment coordinator task, so the task has an air vehicle state from the local vehicle.
* At five seconds the coordinated automation request is sent in which starts the assignment process.
* After receiving the coordinated automation request, the assignment coordinator task send out an 'AssignmentCoordination' message containg the state that the local vehicle will use for planning.
* The 'AssignmentCoordination' is picked up by the 'LmcpObjectNetworkZeroMqZyreBridge' and sent to the other running copy of UxAS
* The assignment coordinator recieves the 'AssignmentCoordination' message from the UxAS and checks to see if its time to send in a TaskAutomationRequest. The 'CoordinatedAutomationRequest' specifies three vehicle IDs and since the the third vehicle is not present, the assignment coordinator must wait untile the specified has passed, 10 seconds from recipt of the request, to sent out the 'TaskAutomationRequest'.
* Once the timer has expired, a 'TaskAutomationRequest' specifing two vheicles is sent out. This causes the UxAS services to calculate assignments for both vehicle.
* The resulting assignment can be plotted using the python scripts located in the sub-directory of '03_Example_DistributedCooperation/UAV_1000/datawork/AutomationDiagramDataService/'

### Things to Try:
1. Edit the automation request, '03_Example_DistributedCooperation/MessagesToSend/CoordinatedAutomationRequest.xml' and comment out, or remove the entry '<int64>3000</int64>' in the 'EntityList'. Rerun the example. Since it will have 'AssignmentCoordination' for all of the requested vehicle, the assignment coordinator will not have to wait until the end of the 'MaximumResponseTime' to start the assignment process.


