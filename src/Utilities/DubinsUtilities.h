/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/* 
 * File:   DubinsUtilities.h
 * Author: jon
 *
 * Created on June 22, 2018, 10:27 AM
 */

#include <vector>
#include "../VisilibityLib/visilibity.h"

#ifndef DUBINSUTILITIES_H
#define DUBINSUTILITIES_H

namespace uxas {
    namespace common {
        namespace utilities {

            /*! \class DubinsConfiguration
             *  \brief This class represents the configuration of a start or end point of a dubins path. This is used to configure the DubinsPath
             *
             */
            class DubinsConfiguration {
            public:

                DubinsConfiguration(double northPosition, double eastPosition, double heading) : northPosition(northPosition), eastPosition(eastPosition), heading(heading) {
                }

                double getX() {
                    return eastPosition;
                }

                double getY() {
                    return northPosition;
                }

                double getHeading() {
                    return heading;
                }

            private:
                //the north position of the constrained vehicle
                double northPosition;
                //the east position of the constrained vehicle
                double eastPosition;
                //the orientation of the constrained vehicle [radians]
                double heading;
            };

            
            /*! \class DubinsWaypoint
             *  \brief This class represents a dubins waypoint
             *
             */
            class DubinsWaypoint {
            public:

                DubinsWaypoint() {
                }

                DubinsWaypoint(double x, double y, double len, double tx, double ty, int turndir) :
                x(x), y(y), len(len), tx(tx), ty(ty), turnDir(turndir) {
                }

            public:
                //the east value
                double x{0.0};
                //the north value
                double y{0.0};
                //the length of the segment from the previous waypoint
                double len{0.0};
                //the east location from the center of the turn
                double tx{0.0};
                //the north location from the center of the turn
                double ty{0.0};
                //the direction the the turn where 1 is ccw, -1 is cw, and 0 is no turn 
                int turnDir{0};
            };

            /*! \class DubinsPath
             *  \brief This class represents a Dubin's path. This class 
             *         calculates and contains Dubin's waypoints in a Dubin's path
             *         based on the start and end configurations
             */
            class DubinsPath {
            public:

                DubinsPath(double x1, double y1, double heading1, double x2, double y2, double heading2, double radius) :
                startDubinsConfiguration(y1, x1, heading1), endDubinsConfiguration(y2, x2, heading2), radius(radius) {
                }

                DubinsPath(DubinsConfiguration startConfiguration, DubinsConfiguration endConfiguration, double radius) : startDubinsConfiguration(startConfiguration), endDubinsConfiguration(endConfiguration), radius(radius) {
                }

            public:
                std::vector<DubinsWaypoint> getDubinsWaypoints();

            private:
                /**\brief A method that is called the first time getDubinsWaypoints is called.
                 *        This creates the Dubin's path between two heading/position pairs.
                 *        This method uses the startConfiguration and endConfiguration as the pair,
                 *        and the radius as the turn radius of the vehicle to calculate the Dubin's path.
                 *        The calculation uses a brute force approach by trying all six possible configurations:
                 *        LRL, RLR, LSL, LSR, RSL, RSR.
                 *        see <http://msl.cs.uiuc.edu/planning/node821.html>
                 * 
                 */       
                void calculateDubinsWaypoints();

                /**\brief A helper function for wrapping an angle
                 * @param theat: angle being wrapped
                 * @return wrapped angle
                 */                
                double wrapAngle(double theta);

                /**\brief A helper function for calculating the cost of a path
                 * @param waypoints: A set of Dubin's waypoints
                 * @return The cost in terms of length of path.
                 */
                double calcPathCost(const std::vector<DubinsWaypoint> &waypoints);

                /**\brief A helper function for a floating point modulo operatio.
                 *        This is the equivalent of MATLAB's mod function.
                 *        Think of this as x % y with decimals in the remainder.
                 * @param x: the number of interest
                 * @param y: the divisor
                 * @return the ramainder
                 */
                double realMod(double x, double y);


            private:
                //The start Dubin's waypoint configuration.
                DubinsConfiguration startDubinsConfiguration;

                //The end Dubin's waypoint configuration
                DubinsConfiguration endDubinsConfiguration;

                //the turn radius for the Dubin's waypoints
                double radius;

                //An ordered list of Dubin's waypoints for the Dubin's path.
                std::vector<DubinsWaypoint> dubinsWaypoints;
            };


        }
    }
}
#endif /* DUBINSUTILITIES_H */

