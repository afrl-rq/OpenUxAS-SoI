Angled Area Search Task
=======================

The angled area search task is an area search task with a specified sweep angle.

Files:
------

* `cfg_AngledAreaSearchTask.xml` - The UxAS configuration file for this example. This configuration file sets up the services and bridges.
* `runUxAS_AngledAreaSearchTask.py` - This script runs UxAS with the details in the UxAS configuration file
* `runAMASE_AngledAreaSearchTask.py` - This script runs AMASE with the AMASE configuration file.
* `Scenario_AngledAreaSearchTask.xml` - The AMASE configuration file for this example.
* `MessagesToSend/` - Contains the messages send by UxAS with the send messages service.
* `MessagesToSend/AirVehicleConfiguration_V101.xml` - Details for air vehicle 101.
* `MessagesToSend/AirVehicleState_V101.xml` - Air vehicle 101's initial state.
* `MessagesToSend/AngledAreaSearchTask_100.xml` - The angled area search task that will be performed by vehicle 101.
* `MessagesToSend/AreaOfInterest_1.xml` - The area of interest that will be searched in the angled area search task.
* `MessagesToSend/AutomationRequest_AngledAreaSearchTask.xml` - The automation request for the angled area search task

Running the example:
--------------------
1. Open a terminal window in the directory: "examples/tasks/AngledAreaSearchTask"
2. enter the command `python3 runUxAS_AngledAreaSearchTask.py` or `./runUxAS_AngledAreaSearchTask.py`
3. open another terminal window in the directory: "examples/tasks/AngledAreaSearchTask"
4. enter the command `python3 runAMASE_AngledAreaSearchTask.py` or `./runAMASE_AngledAreaSearchTask.py`
5. start the AMASE simulation (i.e. press the play button)

### What happens?
* When the AMASE simulation starts, UAV 101 will be initialized and begin flying east.
* After 1.2 seconds the automation request is sent and UxAS begins the mission
* Once the plans have been calculated, UAV 101 will being performing the angled area search task.
