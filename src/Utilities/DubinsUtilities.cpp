/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/* 
 * File:   DubinsUtilities.cpp
 * Author: jon
 * 
 * Created on June 22, 2018, 10:27 AM
 */

#include "DubinsUtilities.h"
#include "Constants/Convert.h"
#include <math.h>
#include "../VisilibityLib/visilibity.h"
#include "Constants/Constant_Strings.h"
#include <float.h>


namespace uxas {
    namespace common {
        namespace utilities {

            std::vector<DubinsWaypoint> DubinsPath::getDubinsWaypoints() {
                if (dubinsWaypoints.empty()) {
                    calculateDubinsWaypoints();
                }
                return dubinsWaypoints;
            };

            void DubinsPath::calculateDubinsWaypoints() {
                //calculate the Dubin's path
                //first translate the aircraft coordinates to standard coordinates
                VisiLibity::Point startLocation = VisiLibity::Point(startDubinsConfiguration.getX(), startDubinsConfiguration.getY());
                double psi1 = wrapAngle(n_Const::c_Convert::dPiO2() - wrapAngle(startDubinsConfiguration.getHeading()));

                VisiLibity::Point endLocation = VisiLibity::Point(endDubinsConfiguration.getX(), endDubinsConfiguration.getY());
                double psi2 = wrapAngle(n_Const::c_Convert::dPiO2() - wrapAngle(endDubinsConfiguration.getHeading()));

                //make the start waypoint
                DubinsWaypoint startWaypoint = DubinsWaypoint(startDubinsConfiguration.getX(), startDubinsConfiguration.getY(), 0.0, startDubinsConfiguration.getX(), startDubinsConfiguration.getY(), 0);
                std::vector<DubinsWaypoint> tmpDubinsWaypoints;
                //make a very expensive waypoint
                DubinsWaypoint maxCostWaypoint = DubinsWaypoint(0, 0, DBL_MAX, 0, 0, 0);
                dubinsWaypoints.push_back(maxCostWaypoint); //create a max cost waypoint list
                //set up waypoint list
                tmpDubinsWaypoints.push_back(startWaypoint);

                //now calculate the turning circles
                VisiLibity::Point startLeftCircle = VisiLibity::Point(startLocation.x() + (-1 * radius * std::sin(psi1)), startLocation.y() + (radius * std::cos(psi1)));
                VisiLibity::Point startRightCircle = VisiLibity::Point(startLocation.x() + (radius * std::sin(psi1)), startLocation.y() + (-1 * radius * std::cos(psi1)));
                VisiLibity::Point endLeftCircle = VisiLibity::Point(endLocation.x() + (-1 * radius * std::sin(psi2)), endLocation.y() + (radius * std::cos(psi2)));
                VisiLibity::Point endRightCircle = VisiLibity::Point(endLocation.x() + (radius * std::sin(psi2)), endLocation.y() + (-1 * radius * std::cos(psi2)));

                VisiLibity::Point v, nextPosition;
                double theta, alpha, gamma;
                //path 1, LRL path
                double distance = VisiLibity::distance(startLeftCircle, endLeftCircle);
                if (distance < 4 * radius) {
                    v = endLeftCircle - startLeftCircle;
                    theta = wrapAngle(std::atan2(v.y(), v.x()) + std::acos(distance / (4 * radius)) + n_Const::c_Convert::dPiO2());
                    alpha = realMod(theta - psi1, n_Const::c_Convert::dTwoPi());
                    double beta = n_Const::c_Convert::dPi() + 2 * std::acos(distance / (4 * radius));
                    double delta = wrapAngle(theta - beta);
                    gamma = realMod(psi2 - delta, n_Const::c_Convert::dPi());

                    //set up the second waypoint
                    VisiLibity::Point nextPosition = VisiLibity::Point::rotate(startLocation - startLeftCircle, alpha) + startLeftCircle;
                    //push back the second waypoint
                    tmpDubinsWaypoints.push_back(DubinsWaypoint(nextPosition.x(), nextPosition.y(), radius * alpha, startLeftCircle.x(), startLeftCircle.y(), 1));
                    //set up third waypoint
                    nextPosition = VisiLibity::Point::rotate(endLocation - endLeftCircle, -1 * gamma) + endLeftCircle;
                    VisiLibity::Point turnPosition = VisiLibity::Point(2 * radius * std::cos(theta - n_Const::c_Convert::dPiO2()), 2 * radius * std::sin(theta - n_Const::c_Convert::dPiO2())) + startLeftCircle;
                    //push back the third waypoint
                    tmpDubinsWaypoints.push_back(DubinsWaypoint(nextPosition.x(), nextPosition.y(), radius * beta, turnPosition.x(), turnPosition.y(), -1));
                    //push back the fourth waypoint
                    tmpDubinsWaypoints.push_back(DubinsWaypoint(endLocation.x(), endLocation.y(), radius * gamma, endLeftCircle.x(), endLeftCircle.y(), 1));

                    //assign tmpDubinsWaypoints to dubinsWaypoints if it has a lower path cost
                    if (calcPathCost(tmpDubinsWaypoints) < calcPathCost(dubinsWaypoints)) {
                        dubinsWaypoints = tmpDubinsWaypoints;
                    }
                    //reset tmp waypoints for next tested path
                    tmpDubinsWaypoints.clear();
                    tmpDubinsWaypoints.push_back(startWaypoint);

                }

                //path 2, RLR path
                distance = VisiLibity::distance(startRightCircle, endRightCircle);
                if (distance < 4 * radius) {
                    v = endRightCircle - startRightCircle;
                    theta = wrapAngle(std::atan2(v.y(), v.x()) - std::acos(distance / (4 * radius)) - n_Const::c_Convert::dPiO2());
                    alpha = realMod(psi1 - theta, n_Const::c_Convert::dPi());
                    double beta = n_Const::c_Convert::dPi() + 2 * std::acos(distance / (4 * radius));
                    double delta = wrapAngle(theta + beta);
                    gamma = realMod(delta - psi2, n_Const::c_Convert::dTwoPi());

                    //set up second waypoint
                    VisiLibity::Point nextPosition = VisiLibity::Point::rotate(startLocation - startRightCircle, -1 * alpha) + startRightCircle;
                    //push back the second waypoint
                    tmpDubinsWaypoints.push_back(DubinsWaypoint(nextPosition.x(), nextPosition.y(), radius * alpha, startRightCircle.x(), startRightCircle.y(), -1));
                    //set up the third waypoint
                    nextPosition = VisiLibity::Point::rotate(endLocation - endRightCircle, gamma) + endRightCircle;
                    VisiLibity::Point turnPosition = VisiLibity::Point(2 * radius * std::cos(theta + n_Const::c_Convert::dPiO2()), 2 * radius * std::sin(theta + n_Const::c_Convert::dPiO2())) + startRightCircle;
                    //push back the third waypoint
                    tmpDubinsWaypoints.push_back(DubinsWaypoint(nextPosition.x(), nextPosition.y(), radius * beta, turnPosition.x(), turnPosition.y(), 1));
                    //push back the fourth waypoint
                    tmpDubinsWaypoints.push_back(DubinsWaypoint(endLocation.x(), endLocation.y(), radius * gamma, endRightCircle.x(), endRightCircle.y(), -1));
                    //assign tmpDubinsWaypoints to dubinsWaypoints if it has a lower path cost
                    if (calcPathCost(tmpDubinsWaypoints) < calcPathCost(dubinsWaypoints)) {
                        dubinsWaypoints = tmpDubinsWaypoints;
                    }
                    //reset tmpDubinsWaypoints for next path
                    tmpDubinsWaypoints.clear();
                    tmpDubinsWaypoints.push_back(startWaypoint);

                }

                //path 3, LSL
                v = endLeftCircle - startLeftCircle;
                distance = VisiLibity::distance(endLeftCircle, startLeftCircle);
                theta = std::atan2(v.y(), v.x());
                alpha = realMod(theta - psi1, n_Const::c_Convert::dTwoPi());
                gamma = realMod(psi2 - theta, n_Const::c_Convert::dTwoPi());

                //set up second waypoint
                nextPosition = VisiLibity::Point::rotate(startLocation - startLeftCircle, alpha) + startLeftCircle;
                //push back second waypoint
                tmpDubinsWaypoints.push_back(DubinsWaypoint(nextPosition.x(), nextPosition.y(), radius * alpha, startLeftCircle.x(), startLeftCircle.y(), 1));
                //set up third waypoint
                nextPosition = VisiLibity::Point::rotate(endLocation - endLeftCircle, -1 * gamma) + endLeftCircle;

                //push back the third waypoint
                tmpDubinsWaypoints.push_back(DubinsWaypoint(nextPosition.x(), nextPosition.y(), distance, nextPosition.x(), nextPosition.y(), 0));
                //push back the fourth waypoint
                tmpDubinsWaypoints.push_back(DubinsWaypoint(endLocation.x(), endLocation.y(), radius * gamma, endLeftCircle.x(), endLeftCircle.y(), 1));

                //assign tmpDubinsWaypoints to dubinsWaypoints if it has a lower path cost
                if (calcPathCost(tmpDubinsWaypoints) < calcPathCost(dubinsWaypoints)) {
                    dubinsWaypoints = tmpDubinsWaypoints;
                }
                //reset tmpDubinsWaypints for next path
                tmpDubinsWaypoints.clear();
                tmpDubinsWaypoints.push_back(startWaypoint);


                //path 4, LSR
                distance = VisiLibity::distance(startLeftCircle, endRightCircle);
                if (distance >= 2 * radius) {
                    v = endRightCircle - startLeftCircle;
                    theta = wrapAngle(std::atan2(v.y(), v.x()) - std::acos(2 * radius / distance) + n_Const::c_Convert::dPiO2());
                    alpha = realMod(theta - psi1, n_Const::c_Convert::dTwoPi());
                    double gamma = realMod(theta - psi2, n_Const::c_Convert::dTwoPi());
                    //set up second waypoint
                    nextPosition = VisiLibity::Point::rotate(startLocation - startLeftCircle, alpha) + startLeftCircle;
                    //push back second waypoint
                    tmpDubinsWaypoints.push_back(DubinsWaypoint(nextPosition.x(), nextPosition.y(), radius * alpha, startLeftCircle.x(), startLeftCircle.y(), 1));
                    //set up third waypoint
                    nextPosition = VisiLibity::Point::rotate(endLocation - endRightCircle, gamma) + endRightCircle;
                    distance = VisiLibity::distance(VisiLibity::Point(tmpDubinsWaypoints[1].x, tmpDubinsWaypoints[1].y), nextPosition);
                    //push back third waypoint
                    tmpDubinsWaypoints.push_back(DubinsWaypoint(nextPosition.x(), nextPosition.y(), distance, nextPosition.x(), nextPosition.y(), 0));
                    //push back the fourth waypoint
                    tmpDubinsWaypoints.push_back(DubinsWaypoint(endLocation.x(), endLocation.y(), radius * gamma, endRightCircle.x(), endRightCircle.y(), -1));

                    //assign tmpDubinsWaypoints to dubinsWaypoints if it has a lower path cost
                    if (calcPathCost(tmpDubinsWaypoints) < calcPathCost(dubinsWaypoints)) {
                        dubinsWaypoints = tmpDubinsWaypoints;
                    }
                    //reset tmpDubinsWaypoints for next tested path
                    tmpDubinsWaypoints.clear();
                    tmpDubinsWaypoints.push_back(startWaypoint);

                }


                //path 5, RSL
                distance = VisiLibity::distance(startRightCircle, endLeftCircle);
                if (distance >= 2 * radius) {
                    v = endLeftCircle - startRightCircle;
                    theta = wrapAngle(std::atan2(v.y(), v.x()) + std::acos(2 * radius / distance) - n_Const::c_Convert::dPiO2());
                    alpha = realMod(psi1 - theta, n_Const::c_Convert::dTwoPi());
                    double gamma = realMod(psi2 - theta, n_Const::c_Convert::dTwoPi());
                    //set up second waypoint
                    nextPosition = VisiLibity::Point::rotate(startLocation - startRightCircle, -1 * alpha) + startRightCircle;
                    //push back second waypoint
                    tmpDubinsWaypoints.push_back(DubinsWaypoint(nextPosition.x(), nextPosition.y(), radius * alpha, startRightCircle.x(), startRightCircle.y(), -1));
                    //set up the third waypoint
                    nextPosition = VisiLibity::Point::rotate(endLocation - endLeftCircle, -1 * gamma) + endLeftCircle;
                    distance = VisiLibity::distance(VisiLibity::Point(tmpDubinsWaypoints[1].x, tmpDubinsWaypoints[1].y), nextPosition);
                    //push back the third waypoint
                    tmpDubinsWaypoints.push_back(DubinsWaypoint(nextPosition.x(), nextPosition.y(), distance, nextPosition.x(), nextPosition.y(), 0));
                    //push back the fourth waypoint
                    tmpDubinsWaypoints.push_back(DubinsWaypoint(endLocation.x(), endLocation.y(), radius * gamma, endLeftCircle.x(), endLeftCircle.y(), 1));
                    //assign tmpDubinsWaypoints to dubinsWaypoints if it has a lower path cost
                    if (calcPathCost(tmpDubinsWaypoints) < calcPathCost(dubinsWaypoints)) {
                        dubinsWaypoints = tmpDubinsWaypoints;
                    }
                    //reset the tmpDubinsWaypoints for next tested path
                    tmpDubinsWaypoints.clear();
                    tmpDubinsWaypoints.push_back(startWaypoint);

                }

                //path 6, RSR
                v = endRightCircle - startRightCircle;
                distance = VisiLibity::distance(endRightCircle, startRightCircle);
                theta = std::atan2(v.y(), v.x());
                alpha = realMod(psi1 - theta, n_Const::c_Convert::dTwoPi());
                gamma = realMod(theta - psi2, n_Const::c_Convert::dTwoPi());

                //set up second waypoint
                nextPosition = VisiLibity::Point().rotate(startLocation - startRightCircle, -1 * alpha) + startRightCircle;
                //push back the second waypoint
                tmpDubinsWaypoints.push_back(DubinsWaypoint(nextPosition.x(), nextPosition.y(), radius * alpha, startRightCircle.x(), startRightCircle.y(), -1));
                //set up the third waypoint
                nextPosition = VisiLibity::Point().rotate(endLocation - endRightCircle, gamma) + endRightCircle;
                //push back the third waypoint
                tmpDubinsWaypoints.push_back(DubinsWaypoint(nextPosition.x(), nextPosition.y(), distance, nextPosition.x(), nextPosition.y(), 0));
                //push back the fourth waypoint
                tmpDubinsWaypoints.push_back(DubinsWaypoint(endLocation.x(), endLocation.y(), radius * gamma, endRightCircle.x(), endRightCircle.y(), -1));

                if (calcPathCost(tmpDubinsWaypoints) < calcPathCost(dubinsWaypoints)) {
                    dubinsWaypoints = tmpDubinsWaypoints;
                }
            };

            double DubinsPath::calcPathCost(const std::vector<DubinsWaypoint> &waypoints) {
                if (waypoints.size() == 0) {
                    return 0.0;
                }

                double cost = 0.0;

                for (unsigned i = 0; i < waypoints.size(); i++) {
                    cost = cost + waypoints[i].len;
                }
                return cost;
            };

            double DubinsPath::wrapAngle(double theta) {
                double a = realMod(theta, n_Const::c_Convert::dTwoPi());
                return a > n_Const::c_Convert::dPi() ? a - n_Const::c_Convert::dTwoPi() : a;
            }

            double DubinsPath::realMod(double x, double y) {
                double ans = std::fmod(x, y);
                return ans >= 0 ? ans : ans + y;
            }

        }
    }
}