waypoint_manager
================================================================================

This SPARK Ada project provides an implementation of the UxAS waypoint_manager, developed as part of a TIM in Dayton, involving collaboration with Dependable Computing, and Rockwell Collins. The implementation was refined by Dependable Computing through additional discussions with AdaCore. 


The proof can be completed with the following invocation of gnatprove in about 12 seconds:

		gnatprove -Pwaypoint_manager.gpr -j7 --level=2


The implementation consists of two primary functions:

- fill_win  (fill window)
- find_wp   (find waypoint)

All other functions are "ghost" functions, used for the purposes of simplifying proof constraints only.  

The fill window function (fill_win) is the more complex function, containing 9 post-conditions in the ads file. The nature of these post-conditions is further documented inline in the ads file. 