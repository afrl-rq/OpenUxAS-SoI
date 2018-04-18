#	Collision Dectection in UxAS using NASA's DAIDALUS code

This example is intended to informally test UxAS integration with NASA's DAIDALUS code.

To demonstrate this integration of DAIDALUS into UxAS a scenario was created that has a point search task that needs to be fulfilled by three eligible entities.  These entities are initially placed 3600 meters from the point to be surveilled.  These entities are also set to collide at the point of interest.  Entity 1000 has a heading of 90 degrees (as measured from true North).  Entity 2000 has a heading of 270 degrees.  Entity 4208 has a heading of 180 degrees.  The expected behavior of this scenario is to have vehicle state information passed to DAIDADLUS which then determines if a violation of the well-clear volume for the ownship is detected within the configured look ahead window.  If a violation is detected, DAIDALUS returns to UxAS the interval that will lead to the violation with respect to ground track maneuvers, ground speed maneuvers, vertical speed maneuvers, and altitude maneuvers.  

## Input Files
* `cfgCollision_1000.xml` - Configuration file for Entity 1000
* `cfgCollision_2000.xml` - Configuration file for Entity 2000
* `cfgCollision_4208.xml` - Configuration file for Entity 4208
* `collision_mkii.xml` - AMASE configuration file for scenario
* `runUxAS_Collision.sh` - script file that launches the scenario

## Running the Example
1. Open a terminal window in the directory `examples/00_Collision`
2. Run the command `sh runUxAS_Collision.sh`
3. Zoom in on the AMASE window until the Keep in Zone is visible
4. Press play

## Notes
1. The vehicle configuration files may need to be edited to correctly identify the network device on line 9.
2. Three terminals will open and display to the screen debugging messages from DAIDALUS information.
3. The logged messages need to be interrogated in order to view UxAS messages sent from DAIDALUS information.
4. This is a work in progress and is subject to change.
