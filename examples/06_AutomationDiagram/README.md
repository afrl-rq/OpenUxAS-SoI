# AutomationDataDiagramService Example

This example is intended to both informally test UxAS's AutomationDataDiagramService and demonstrate how to use it.

Each time UxAS is run with the AutomationDataDiagramService enabled, directories containing Python code are created, one per AutomationResponse. This Python code plots visualizations of the tasks and zones involved in an AutomationResponse, along with the planned paths for each vehicle. Note that since the exact paths that will be flown for certain tasks are unknown during the planning phase (e.g., for MultiVehicleWatchTasks and EscortTasks under certain conditions), UxAS uses simple approximations these tasks. Therefore, planned paths containing these tasks do not represent an accurate simulation. However, they are still useful for visualizing the approximate paths that were used to determine the AutomationResponse.

This example assumes knowledge of the AMASE Setup Tool, which is demonstrated in OpenUxAS/examples/05_AssignTasks. The AMASE Setup Tool is used to create a "skeleton" scenario file that must be modified slightly by hand to work with UxAS, since this particular example includes some tasks not fully supported by AMASE. Then, since UxAS requires all scenario events to be sent in individually, the Python script amase2uxas.py is used to parse the modified scenario file, save each scenario event in its own file, and create a "stub" for configuring UxAS's SendMessagesService to send the events to UxAS. This stub is then added to UxAS's main configuration file, UxAS is run, and the Python scripts produced by UxAS are run.

## Input Files:
* `AutomationDiagram_cfg.xml` - UxAS configuration file
* `AutomationDiagramAmaseSkeleton.xml` - The original scenario file created using the AMASE Setup Tool.
* `AutomationDiagramScenario.xml` - The modified scenario file parsed by amase2uxas.py
* `runUxAS_AutomationDiagram.sh` - shell script that runs the example
* `runUxAS_AutomationDiagram.bat` - Windows script that runs the example

## Running the Example:




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


