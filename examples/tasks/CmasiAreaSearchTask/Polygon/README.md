Area Search Task
=======================

A task for searching an area.

Files:
------

* `cfg_AreaSearchTask.xml` - The UxAS configuration file for this example. This configuration file sets up the services and bridges.
* `runUxAS_AreaSearchTask.py` - This script runs UxAS with the details in the UxAS configuration file
* `runAMASE_AreaSearchTask.py` - This script runs AMASE with the AMASE configuration file.
* `Scenario_AreaSearchTask.xml` - The AMASE configuration file for this example.
* `MessagesToSend/` - Contains the messages send by UxAS with the send messages service.
* `MessagesToSend/AirVehicleConfiguration_V101.xml` - Details for air vehicle 101.
* `MessagesToSend/AirVehicleState_V101.xml` - Air vehicle 101's initial state.
* `MessagesToSend/AreaSearchTask_100.xml` - The area search task task to be performed by vehicle 101.
* `MessagesToSend/AutomationRequest_AreaSearch.xml` - The automation request for the area search task.


Running the example:
--------------------
1. Open a terminal window in the directory: "examples/tasks/CmasiAreaSearch/Circle"
2. enter the command `python3 runUxAS_AreaSearchTask.py` or `./runUxAS_AreaSearchTask.py`
3. open another terminal window in the directory: "examples/tasks/CmasiAreaSearch/Circle"
4. enter the command `python3 runAMASE_AreaSearchTask.py` or `./runAMASE_AreaSearchTask.py`
5. start the AMASE simulation (i.e. press the play button)

### What happens?
* When the AMASE simulation starts, vehicle 101 will be initialized and begin flying east.
* After 4 seconds, an automation request for the area search task is sent.
* Once plan have been calculated, UAV 101 will being performing the area search task.
