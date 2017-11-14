# AutomationDataDiagramService Example

This example is intended to both informally test UxAS's AutomationDataDiagramService and demonstrate how to use it.

Each time UxAS is run with the AutomationDataDiagramService enabled, directories containing Python code are created, one directory per AutomationResponse. This Python code plots visualizations of the tasks and zones involved in an AutomationResponse, along with the planned paths for each vehicle. Note that since the exact paths that will be flown for certain tasks are unknown during UxAS's planning phase (e.g., for MultiVehicleWatchTasks and EscortTasks under certain conditions), UxAS uses simple approximations for these tasks. Therefore, planned paths containing these tasks do not represent an accurate simulation. However, they are still useful for visualizing the approximate paths that were used to determine the AutomationResponse.

This example assumes knowledge of the AMASE Setup Tool, which is demonstrated in OpenUxAS/examples/05_AssignTasks. The AMASE Setup Tool is used to create a "skeleton" scenario file that must be modified slightly by hand to work with UxAS, since this particular example includes some tasks not fully supported by AMASE. Then, since the AMASE Setup Tool saves all scenario events in a single scenario file but UxAS requires all scenario events to be sent in individually, the Python script amase2uxas.py is used to parse the modified scenario file, save each scenario event in its own file, and create a "stub" for configuring UxAS's SendMessagesService to send the events to UxAS. This stub is then added to UxAS's main configuration file, UxAS is run, and the Python scripts produced by UxAS are run.

## Input Files:
* `AutomationDiagram_cfg.xml` - UxAS configuration file
* `AutomationDiagramAmaseSkeleton.xml` - The original scenario file created using the AMASE Setup Tool.
* `AutomationDiagramScenario.xml` - The modified scenario file parsed by amase2uxas.py
* `runUxAS_AutomationDiagram.sh` - shell script that runs the example

## Running the Example:
1. Open a terminal window in the directory `examples/06_AutomationDiagram`
2. Run the command `../../resources/amase2uxas.py AutomationDiagramScenario.xml`, which creates a directory `MessagesToSend` filled with LMCP messages and a configuration stub `SendMessagesService_cfg.xml`. In this example, this stub has already been copied into `AutomationDiagram_cfg.xml`. If you run into permissions issues, run the command `chmod 777 ../../resources/amase2uxas.py` and try again
3. Run the command `./runUxAS_AutomationDiagram.sh`
4. Go to directory `examples/06_AutomationDiagram/` `RUNDIR_AutomationDiagram/datawork/` `AutomationDiagramDataService/` `0001_AutomationDiagramID0100_xxx` and run the Python script `PlotAutomationDiagram.py`, which creates a diagram
5. View the saved output PDF `AutomationDiagram.pdf`




## The Workflow for Setting Up the Scenario File:
Setting up scenarios for UxAS can be challenging without a visualization to see where tasks and zones are located. AMASE provides a graphical Setup Tool that allows users to setup scenarios while visualing tasks and zones. See `examples/05_AssignTasks` for a basic walkthrough on using the AMASE Setup Tool to setup a scenario for UxAS.

The AMASE Setup Tool allows users to add any type of event to a scenario file. More specifically, a user can add any event encoded in the LMCP library AMASE uses, which needs to be kept in sync with the LMCP library UxAS uses. A challenge is that AMASE only provides methods for creating and visualizing tasks on the map for tasks in the CMASI LMCP MDM. UxAS implements extensions to these tasks with more options, mainly in the IMPACT LMCP MDM. To setup a scenario file in the AMASE Setup Tool with tasks from IMPACT, we therefore use the AMASE Setup Tool's Event Editor to create IMPACT tasks with as many fields completed as possible (i.e. any fields that don't need to be created and visualized on the map), then create corresponding tasks from CMASI using the Map Display (i.e., creating and visualizing them on the map). These CMASI tasks are then used to fill in the missing fields of the IMPACT tasks though a bit of manual editing.

In this example, the scenario file `AutomationDiagramAmaseSkeleton.xml` was created using the AMASE Setup Tool. You can load this scenario file by running the command `sh <your_path_prefix>/OpenAMASE/OpenAMASE/run/linux/SetupTool.sh` 
and opening this file in the resulting GUI. In this example, you will see a number of PointSearchTasks, LineSearchTasks, and AreaSearchTasks visualized on the map. Several of these are used to fill in details of IMPACT tasks. The general idea is to create the full `AutomationDiagramAmaseSkeleton.xml` file first, save it as `AutomationDiagramScenario.xml` when finished, then make manual modifications to `AutomationDiagramScenario.xml`. The following describes the suggested general approach, organized by task type.

### For AngledAreaSearchTasks
* For each AngledAreaSearchTask with TaskID __x__ in the AMASE scenario, create:
  * An AreaOfInterest with AreaID 1__x__ that has a blank Area.
  * A nearly complete AngledAreaSearchTask referencing the AreaOfInterest.
  * An AreaSearchTask with TaskID 2__x__ that only includes a SearchArea.
  * If a StartPoint is required, a PointSearch task with TaskID 3__x__ that only includes a Location.
* When modifying the UxAS scenario file `AutomationDiagramScenario.xml` that was generated from the AMASE `AutomationDiagramAmaseSkeleton.xml` scenario file:
  * Copy the AreaSearchTask's SearchArea into the AreaOfInterest's Area.
  * Delete the AreaSearchTask.
  * If there is a StartPoint, copy the PointSearchTask's Location into the AngledAreaSearchTask's StartPoint.
  * Delete the PointSearchTask (if applicable).

### For ImpactLineSearchTasks
  
* For each ImpactLineSearchTask with TaskID __x__ in the AMASE scenario, create:
  * A LineOfInterest with LineID 1__x__ that has a blank Line.
  * A nearly complete ImpactLineSearchTask referencing the LineOfInterest.
  * A LineSearchTask with TaskID 2__x__ that only includes a PointList.
* When modifying the UxAS scenario file `AutomationDiagramScenario.xml` that was generated from the AMASE `AutomationDiagramAmaseSkeleton.xml` scenario file:
  * Copy the LineSearchTask's PointList into the LineOfInterest's Line.
  * Delete the LineSearchTask.
  
### For ImpactPointSearchTasks

* For each ImpactPointSearchTask with TaskID __x__ in the AMASE scenario, create:
  * A PointOfInterest with PointID 1__x__ that has a blank Location (if using LocationID).
  * A nearly complete ImpactPointSearchTask (that references the PointOfInterest if using LocationID).
  * A PointSearchTask with TaskID 2__x__ that only includes a SearchLocation.
* When modifying the UxAS scenario file `AutomationDiagramScenario.xml` that was generated from the AMASE `AutomationDiagramAmaseSkeleton.xml` scenario file:
  * Copy the PointSearchTask's SearchLocation into the PointOfInterest's Location (if using SearchLocationID) or into the ImpactPointSearchTask's SearchLocation (if not).
  * Delete the PointSearchTask.
  
### For PatternSearchTasks

* For each PatternSearchTask with TaskID __x__ in the AMASE scenario, create:
  * A PointOfInterest with PointID 1__x__ that has a blank Location (if using LocationID).
  * A nearly complete ImpactPointSearchTask (that references the PointOfInterest if using LocationID).
  * A PointSearchTask with TaskID 2__x__ that only includes a SearchLocation.
* When modifying the UxAS scenario file `AutomationDiagramScenario.xml` that was generated from the AMASE `AutomationDiagramAmaseSkeleton.xml` scenario file:
  * Copy the PointSearchTask's SearchLocation into the PointOfInterest's Location (if using SearchLocationID) or the PatternSearchTask's SearchLocation (if not).
  * Delete the PointSearchTask.

## Using amase2uxas.py:

As mentioned earlier, the AMASE Setup Tool saves all scenario events in a single file, whereas UxAS needs to receive event messages one-by-one. UxAS provides a Service called the `SendMessagesService` that can schedule saved messages to be sent to UxAS at specific times. To support the use of AMASE scenario files with UxAS, the script `amase2uxas.py` in directory `OpenUxAS/resources` reads in an XML file with a `<ScenarioEventList>` element containing elements that are LMCP messages and saves each message as an individual file in the directory `./MessagesToSend`. It names message files according to message type, ID number (if applicable), and a unique identifier (if needed). It also creates a "configuration stub" `./SendMessagesService_cfg.xml` for the `SendMessagesService` that schedules the messages in the order in which they appear in the `<ScenarioEventList>`, with a small delay between all messages except AutomationRequest messages, which have a larger delay. This stub can be copied into a service configuration file used to start UxAS, which in this example is `AutomationDiagram_cfg.xml`. In this example, the stub has already been pasted into this file.

To be able to use `amase2uxas.py` from any location without giving the full path, a user can add directory `<your_path_prefix>/OpenUxAS/resources` to his or her path, e.g., by editing `.bash_profile`.

## Current Limitations:

At the time of writing, the `AutomationDataDiagramService` is not complete. It does not plot every task UxAS implements, and it does not necessarily plot all waypoints for a task. For instance, AngledAreaSearches are often only partially plotted.

