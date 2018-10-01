Point Search Task
=======================

A task where a vehicle searches a point of interest.

Files:
------

* `cfg_PointSearchTask.xml` - The UxAS configuration file for this example. This configuration file sets up the services and bridges.
* `runUxAS_PointSearchtask.py` - This script runs UxAS with the details in the UxAS configuration file
* `runAMASE_PointSearchTask.py` - This script runs AMASE with the AMASE configuration file.
* `Scenario_PointSearchTask.xml` - The AMASE configuration file for this example.
* `MessagesToSend/` - Contains the messages send by UxAS with the send messages service.
* `MessagesToSend/AirVehicleConfiguration_V101.xml` - Details for air vehicle 101.
* `MessagesToSend/AirVehicleState_V101.xml` - Air vehicle 101's initial state.
* `MessagesToSend/PointSearchTask_100.xml` - The point search task that is requested.
* `MessagesToSend/AutomationRequest_PointSearch.xml` - The automation request for the point search task.


Running the example:
--------------------
1. Open a terminal window in the directory: "examples/tasks/CmasiPointSearchTask"
2. enter the command `python3 runUxAS_PointSearchTask.py` or `./runUxAS_PointSearchTask.py`
3. open another terminal window in the directory: "examples/tasks/CmasiPointSearchTask"
4. enter the command `python3 runAMASE_PointSearchTask.py` or `./runAMASE_PointSearchTask.py`
5. start the AMASE simulation (i.e. press the play button)

### What happens?
* When the AMASE simulation starts, vehicle 101 will be initialized and begin flying east.
* After 4 seconds, an automation request for the point search task is sent.
* Once plans have been calculated, vehicle 101 will being performing the point search task.
