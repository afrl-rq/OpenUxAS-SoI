// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

//
//    THIS SOFTWARE AND ANY ACCOMPANYING DOCUMENTATION IS RELEASED "AS IS." THE
//    U.S.GOVERNMENT MAKES NO WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, CONCERNING
//    THIS SOFTWARE AND ANY ACCOMPANYING DOCUMENTATION, INCLUDING, WITHOUT LIMITATION,
//    ANY WARRANTIES OF MERCHANTABILITY OR FITNESS FOR A PARTICULAR PURPOSE. IN NO EVENT
//    WILL THE U.S. GOVERNMENT BE LIABLE FOR ANY DAMAGES, INCLUDING ANY LOST PROFITS,
//    LOST SAVINGS OR OTHER INCIDENTAL OR CONSEQUENTIAL DAMAGES ARISING OUT OF THE USE,
//    OR INABILITY TO USE, THIS SOFTWARE OR ANY ACCOMPANYING DOCUMENTATION, EVEN IF
//    INFORMED IN ADVANCE OF THE POSSIBILITY OF SUCH DAMAGES.
//
// Assignment.h: interface for the CAssignment class.
//
//////////////////////////////////////////////////////////////////////

#if !defined(AFX_ASSIGNMENT_H__CA36AC9A_0A3D_4110_9E0F_7BA1B4C76258__INCLUDED_)
#define AFX_ASSIGNMENT_H__CA36AC9A_0A3D_4110_9E0F_7BA1B4C76258__INCLUDED_

#if _MSC_VER > 1000
#pragma once
#endif // _MSC_VER > 1000

//#include "GlobalDefines.h"
//#include "TrajectoryDefinitions.h"
#include "BaseObject.h"
#include "Waypoint.h"

#include "TaskAssignment.h"

#include <assert.h>

namespace n_FrameworkLib
{

    class CAssignment
    {
    public: //typedefs
        typedef CWaypoint::V_WAYPOINT_t V_WAYPOINT_t;
        typedef CWaypoint::V_WAYPOINT_IT_t V_WAYPOINT_IT_t;
        typedef CWaypoint::V_WAYPOINT_CONST_IT_t V_WAYPOINT_CONST_IT_t;

        typedef CTaskAssignment::V_TASKASSIGNMENT_t V_TASKASSIGNMENT_t;
        typedef CTaskAssignment::V_TASKASSIGNMENT_IT_t V_TASKASSIGNMENT_IT_t;
        typedef CTaskAssignment::V_TASKASSIGNMENT_CONST_IT_t V_TASKASSIGNMENT_CONST_IT_t;

    public:
    public:

        CAssignment(double dDistancePrevious = 0.0)
        : m_dDistanceTotalTemp_m(0),
        m_iWaypointCurrent(-1),
        m_iLastTaskID(-1),
        m_iWaypointID_next(1),
        m_dMinimumWaypointSeparation_m((std::numeric_limits<double>::max)()),
        m_iMaximumNumberWaypoints((std::numeric_limits<int>::max)()),
        m_iMinimumNumberWaypointsForTurn(8),
        m_dMinimumAssignmentSeparation_m(0.0),
        m_dNewAssignmentOnsetDelay_s(0.0),
        m_dDangerDistance((std::numeric_limits<double>::max)()),
        m_dDistanceTotalPrevious_m(dDistancePrevious),
        m_iNumberAssignments(0),
        m_dHeadingFinal_rad(0.0)
 { };

        CAssignment(int iID, double dPositionX_m, double dPositionY_m, double dPositionZ_m, double dHeadingFinal, double dDistancePrevious = 0.0,
                const double& dMinimumWaypointSeparation_m = (std::numeric_limits<double>::max)(),
                const double& dMinimumAssignmentSeparation_m = 0.0,
                const double& dNewAssignmentOnsetDelay_s = 0.0,
                const double& dDistanceAllocatedForAssignedTasks_m = 0.0,
                const int& iMaximumNumberWaypoints = (std::numeric_limits<int>::max)(),
                const int& iMinimumNumberWaypointsForTurn = 8,
                const double& dMaximumTimeEndurance_s = (std::numeric_limits<double>::max)(),
                const double& dDangerDistance = (std::numeric_limits<double>::max)())
        : m_dDistanceTotalTemp_m(0),
        m_iWaypointCurrent(-1),
        m_iLastTaskID(iID),
        m_iWaypointID_next(1),
        m_dMinimumWaypointSeparation_m(dMinimumWaypointSeparation_m),
        m_iMaximumNumberWaypoints(iMaximumNumberWaypoints),
        m_iMinimumNumberWaypointsForTurn(iMinimumNumberWaypointsForTurn),
        m_dMinimumAssignmentSeparation_m(dMinimumAssignmentSeparation_m),
        m_dNewAssignmentOnsetDelay_s(dNewAssignmentOnsetDelay_s),
        m_dDangerDistance(dDangerDistance),
        m_dDistanceTotalPrevious_m(dDistancePrevious),
        m_iNumberAssignments(0),
        m_dHeadingFinal_rad(dHeadingFinal) {
            iAddWaypoint(CWaypoint(dPositionX_m, dPositionY_m, dPositionZ_m));
        };

        virtual ~CAssignment() { };

        // copy constructer

        CAssignment(const CAssignment& rhs) {
            operator=(rhs);
        };

        void operator=(const CAssignment& rhs) {
            vwayGetWaypoints() = rhs.vwayGetWaypoints();
            SetNumberAssignments(rhs.iGetNumberAssignments());
            SetHeadingFinal(rhs.dGetHeadingFinal());
            dGetDistancePrevious() = rhs.dGetDistancePrevious();
            dGetDistanceTemp() = rhs.dGetDistanceTemp();
            iGetWaypointCurrent() = rhs.iGetWaypointCurrent();
            vtaskGetAssignments() = rhs.vtaskGetAssignments();
            iGetLastTaskID() = rhs.iGetLastTaskID();
            iGetWaypointID_next() = rhs.iGetWaypointID_next();

            dGetDistanceAllocatedForAssignedTasks_m() = rhs.dGetDistanceAllocatedForAssignedTasks_m();
            dGetMinimumWaypointSeparation_m() = rhs.dGetMinimumWaypointSeparation_m();
            iGetMaximumNumberWaypoints() = rhs.iGetMaximumNumberWaypoints();
            iGetMinimumNumberWaypointsForTurn() = rhs.iGetMinimumNumberWaypointsForTurn();
            dGetMinimumAssignmentSeparation_m() = rhs.dGetMinimumAssignmentSeparation_m(),
                    dGetNewAssignmentOnsetDelay_s() = rhs.dGetNewAssignmentOnsetDelay_s(),
                    dGetDangerDistance() = rhs.dGetDangerDistance();

        };

    public:

        int iWaypointIndexFromID(const int& iWaypointID) {
            int iIndex(0);
            for (V_WAYPOINT_IT_t itWaypoint = vwayGetWaypoints().begin(); itWaypoint != vwayGetWaypoints().end(); itWaypoint++, iIndex++) {
                if (itWaypoint->iGetID() == iWaypointID) {
                    break;
                }
            }
            if (iIndex >= static_cast<int> (vwayGetWaypoints().size())) {
                iIndex = -1;
            }
            return (iIndex);
        }

        bool bSaveWaypointsToMatlabMatrix(ofstream& ofstrMatlabFile) {
            bool bReturn(false); //will return true if there are any waypoints to print
            if (!vwayGetWaypoints().empty()) {
                ofstrMatlabFile << " [ ...";
                for (V_WAYPOINT_CONST_IT_t itWaypoint = itGetWaypointBegin(); itWaypoint != itGetWaypointEnd(); itWaypoint++) {
                    ofstrMatlabFile << endl << *itWaypoint;
                }
                ofstrMatlabFile << "]";
                bReturn = true;
            } //if(!vwayGetWaypoints().empty())
            return (bReturn);
        };

        void ResetAssignment() {
            vwayGetWaypoints().clear();
            SetNumberAssignments(0);
            SetHeadingFinal(0.0);
            dGetDistancePrevious() = 0;
            dGetDistanceTemp() = 0;
            iGetWaypointCurrent() = -1;
            vtaskGetAssignments().clear();
            iGetLastTaskID() = -1;
        };

        const double dGetCumulativeDistanceCurrent_m(const int& iWaypointLast, const double& dDistanceSinceLastWaypoint) const {
            double dTotalDistance_m = dDistanceSinceLastWaypoint + dGetDistancePrevious();

            if (static_cast<int> (vwayGetWaypoints().size()) > iWaypointLast) {
                int iCountWaypoints = 0;
                for (V_WAYPOINT_CONST_IT_t itWaypoint = vwayGetWaypoints().begin(); itWaypoint != vwayGetWaypoints().end(); itWaypoint++, iCountWaypoints++) {
                    if (iCountWaypoints <= iWaypointLast) {
                        dTotalDistance_m += itWaypoint->dGetSegmentLength();
                    } else {
                        break;
                    }
                }
            }
            return (dTotalDistance_m);
        };

        const double dGetDistanceTotal(bool bUseVisibilityGraph = false) const {
            double dTotalDistance_m = 0.0;
            if (!bUseVisibilityGraph) {
                if (vwayGetWaypoints().size() > 0) {
                    V_WAYPOINT_CONST_IT_t itWaypointLast = vwayGetWaypoints().begin();
                    for (V_WAYPOINT_CONST_IT_t itWaypoint = vwayGetWaypoints().begin(); itWaypoint != vwayGetWaypoints().end(); itWaypoint++) {
                        if (itWaypoint->dGetSegmentLength() > 0.0) {
                            dTotalDistance_m += itWaypoint->dGetSegmentLength();
                        } else if (itWaypoint != vwayGetWaypoints().begin()) {
                            dTotalDistance_m += const_cast<CWaypoint*> (&*itWaypoint)->relativeDistance2D_m(static_cast<CPosition> (*itWaypointLast));
                        }
                        if (itWaypoint != vwayGetWaypoints().begin()) {
                            itWaypointLast++;
                        }
                    }
                }
            } else //if(!bUseVisibilityGraph)
            {
                for (V_TASKASSIGNMENT_CONST_IT_t itTask = vtaskGetAssignments().begin(); itTask != vtaskGetAssignments().end(); itTask++) {
                    dTotalDistance_m += itTask->dGetMinimumTaskCost();
                }
            } //if(!bUseVisibilityGraph)

            return (dTotalDistance_m + dGetDistancePrevious() + dGetDistanceTemp());
        };

        const double dGetDistanceFromFirstWaypointToWaypoint_m(const size_t& szWaypointIndex) const {
            double dReturnDistance_m = 0.0;
            assert(szWaypointIndex < vwayGetWaypoints().size());
            if (vwayGetWaypoints().size() > 0) {
                size_t szCountWaypoints(0);
                for (V_WAYPOINT_CONST_IT_t itWaypoint = vwayGetWaypoints().begin(); itWaypoint != vwayGetWaypoints().end(); itWaypoint++, szCountWaypoints++) {
                    dReturnDistance_m += itWaypoint->dGetSegmentLength();
                    if (szWaypointIndex == szCountWaypoints) {
                        break;
                    }
                }
            }
            return (dReturnDistance_m);
        };

        const double dGetDistanceFromCurrentToEnd_m() const {
            return (dGetDistanceFromWaypointToEnd_m(iGetWaypointCurrent()));
        };

        const double dGetDistanceFromWaypointToEnd_m(const size_t& szWaypointIndex = 0) const {
            double dReturnDistance_m = 0.0;
            assert(szWaypointIndex < vwayGetWaypoints().size());
            if (vwayGetWaypoints().size() > 0) {
                size_t szCountWaypoints(0);
                V_WAYPOINT_CONST_IT_t itWaypoint = vwayGetWaypoints().begin() + szWaypointIndex;
                for (; itWaypoint != vwayGetWaypoints().end(); itWaypoint++, szCountWaypoints++) {
                    dReturnDistance_m += itWaypoint->dGetSegmentLength();
                }
            }
            return (dReturnDistance_m);
        };

        const double dGetTimeAtWaypoint_s(const size_t& szWaypointIndex) const {
            //ASSUMES: the vehicle flys the commanded speed
            //ASSUMES: the commanded speed is in m/sec
            //TODO:: check for mach flag a convert mach to m/sec
            double dSpeedCommandInitial = vwayGetWaypoints().begin()->dGetSpeed_mps();

            double dReturnTime_s = (dSpeedCommandInitial <= 0.0) ? (0.0) : (dGetDistancePrevious() / dSpeedCommandInitial);

            assert(szWaypointIndex < vwayGetWaypoints().size());
            if (vwayGetWaypoints().size() > 0) {
                size_t szCountWaypoints(0);
                for (V_WAYPOINT_CONST_IT_t itWaypoint = vwayGetWaypoints().begin(); itWaypoint != vwayGetWaypoints().end(); itWaypoint++, szCountWaypoints++) {
                    dReturnTime_s += (itWaypoint->dGetSpeed_mps() <= 0.0) ? (0.0) : (itWaypoint->dGetSegmentLength() / itWaypoint->dGetSpeed_mps());
                    if (szWaypointIndex == szCountWaypoints) {
                        break;
                    }
                }
            }
            return (dReturnTime_s);
        };

        bool bInsertWaypoint(const int& iWaypointIndexStart, const double& dDistanceFromLastPoint, CWaypoint::n_enWaypointType_t& typeWaypoint) {
            bool bSuccess(false);

            CBaseObject basePositionHeadingCalculated;
            int iWaypointIndexAfter(0);
            double dNewSegmentLength(0.0);
            if (bCalculateFuturePositionBasedOnDistance(iWaypointIndexStart, dDistanceFromLastPoint, basePositionHeadingCalculated, iWaypointIndexAfter, dNewSegmentLength)) {
                V_WAYPOINT_IT_t itWaypointBefore = vwayGetWaypoints().begin() + (iWaypointIndexAfter - 1);
                V_WAYPOINT_IT_t itWaypointAfter = vwayGetWaypoints().begin() + iWaypointIndexAfter;
                CWaypoint wayTemp = *itWaypointAfter;

                //set up new waypoint
                wayTemp.m_north_m = basePositionHeadingCalculated.m_north_m; //this sets the new position
                wayTemp.m_east_m = basePositionHeadingCalculated.m_east_m; //this sets the new position
                wayTemp.dGetSegmentLength() = dNewSegmentLength;
                wayTemp.SetTypeWaypoint(typeWaypoint);
                wayTemp.SetObjectiveHandle(-1); //just in  case

                //fix original after waypoint
                itWaypointAfter->dGetSegmentLength() -= dNewSegmentLength;

                V_WAYPOINT_IT_t itWaypointNew = vwayGetWaypoints().insert(itWaypointAfter, wayTemp);
            }

            return (bSuccess);
        }

        bool bCalculateFuturePositionBasedOnDistance(const int& iWaypointIndexStart,
                const double& dDistanceToGo,
                CBaseObject& basePositionHeadingCalculated,
                int& iWaypointIndexAfter,
                double& dNewSegmentLength,
                bool bDefaultToLastWaypoint = false) {
            //RAS:: assume iWaypointIndexStart is the waypoint to calculated distance from
            //RAS:: I'm assuming that the heading returned is based on the segment after the waypoint
            bool bReturn(false);
            iWaypointIndexAfter = iWaypointIndexStart + 1;
            if ((iWaypointIndexStart < (static_cast<int> (vwayGetWaypoints().size()) - 1))&&(iWaypointIndexStart >= 0)) {
                // we have a segment we can extrapolate on
                double dDistance(0.0);

                V_WAYPOINT_CONST_IT_t itWaypoint = vwayGetWaypoints().begin() + iWaypointIndexStart;
                V_WAYPOINT_CONST_IT_t itWaypointNext = itWaypoint + 1;

                for (; itWaypointNext != vwayGetWaypoints().end(); itWaypoint++, itWaypointNext++, iWaypointIndexAfter++) {
                    dDistance += itWaypointNext->dGetSegmentLength();
                    if (dDistance >= dDistanceToGo) {
                        //found the segment that we are on
                        if ((dDistance > dDistanceToGo)&&(itWaypointNext->dGetSegmentLength() > 0.0)) {
                            dDistance -= itWaypointNext->dGetSegmentLength();
                            dNewSegmentLength = dDistanceToGo - dDistance;
                            double dFractionOfSegment = dNewSegmentLength / itWaypointNext->dGetSegmentLength();

                            CCircle::enTurnDirection_t turnDirection = itWaypointNext->circleGetTurn().turnGetTurnDirection();
                            if (turnDirection == CCircle::turnNone) {
                                //straight segment
                                double dNorthDifference = itWaypointNext->m_north_m - itWaypoint->m_north_m;
                                double dEastDifference = itWaypointNext->m_east_m - itWaypoint->m_east_m;
                                basePositionHeadingCalculated.dGetHeading() = atan2(dEastDifference, dNorthDifference);
                                CPosition posChangeFromInitalWaypoint = ((CPosition) (*itWaypointNext) - (CPosition) (*itWaypoint)) * dFractionOfSegment + (CPosition) (*itWaypoint);
                                basePositionHeadingCalculated += posChangeFromInitalWaypoint;
                            } else {
                                //curve segment
                                double dAngleTurnFull = itWaypointNext->circleGetTurn().dGetRelativeAngle((*itWaypoint), (*itWaypointNext));
                                double dAngleTurn = dFractionOfSegment*dAngleTurnFull;
                                double dAngleOnCircle = dAngleTurn + itWaypointNext->circleGetTurn().dGetAngle(*itWaypoint);
                                itWaypointNext->circleGetTurn().GetNewHeadingAngleAndPosition(basePositionHeadingCalculated.dGetHeading(),
                                        basePositionHeadingCalculated,
                                        dAngleOnCircle);
                                //need to change angle to heading
                                basePositionHeadingCalculated.dGetHeading() = n_Const::c_Convert::dPiO2() - basePositionHeadingCalculated.dGetHeading();
                                if (turnDirection == CCircle::turnClockwise) {
                                    basePositionHeadingCalculated.dGetHeading() += n_Const::c_Convert::dPi();
                                }
                                basePositionHeadingCalculated += itWaypointNext->circleGetTurn();
                            }
                        } else //if((dDistance > dDistanceToGo)&&(itWaypointNext->dGetSegmentLength()>0.0))
                        {
                            //we are at itWaypointNext
                            CCircle::enTurnDirection_t turnDirection = itWaypointNext->circleGetTurn().turnGetTurnDirection();
                            if (turnDirection == CCircle::turnNone) {
                                //straight segment
                                double dNorthDifference = itWaypointNext->m_north_m - itWaypoint->m_north_m;
                                double dEastDifference = itWaypointNext->m_east_m - itWaypoint->m_east_m;
                                basePositionHeadingCalculated.dGetHeading() = atan2(dEastDifference, dNorthDifference);
                                CPosition posChangeFromInitalWaypoint = (CPosition) (*itWaypointNext);
                                basePositionHeadingCalculated += posChangeFromInitalWaypoint;
                            } else {
                                double dAngleOnCircle = itWaypointNext->circleGetTurn().dGetAngle(*itWaypoint);
                                itWaypointNext->circleGetTurn().GetNewHeadingAngleAndPosition(basePositionHeadingCalculated.dGetHeading(),
                                        basePositionHeadingCalculated,
                                        dAngleOnCircle);
                                basePositionHeadingCalculated.dGetHeading() = n_Const::c_Convert::dPiO2() - basePositionHeadingCalculated.dGetHeading();
                                //need to change angle to heading
                                basePositionHeadingCalculated.dGetHeading() = n_Const::c_Convert::dPiO2() - basePositionHeadingCalculated.dGetHeading();
                                if (turnDirection == CCircle::turnClockwise) {
                                    basePositionHeadingCalculated.dGetHeading() += n_Const::c_Convert::dPi();
                                }
                                basePositionHeadingCalculated += itWaypointNext->circleGetTurn();
                            }
                        } //if((dDistance > dDistanceToGo)&&(itWaypointNext->dGetSegmentLength()>0.0))

                        bReturn = true;
                        break;
                    } //if(dDistance >= dDistanceToGo)

                } //for(;itWaypointNext!=vwayGetWaypoints().end();itWaypoint++,itWaypointNext++)
                if (bDefaultToLastWaypoint && !bReturn) {
                    //we are at the last waypoint
                    if (vwayGetWaypoints().size() > 1) {
                        V_WAYPOINT_CONST_IT_t itWaypoint = vwayGetWaypoints().end() - 2;
                        V_WAYPOINT_CONST_IT_t itWaypointNext = itWaypoint + 1;
                        CCircle::enTurnDirection_t turnDirection = itWaypointNext->circleGetTurn().turnGetTurnDirection();
                        if (turnDirection == CCircle::turnNone) {
                            //straight segment
                            double dNorthDifference = itWaypointNext->m_north_m - itWaypoint->m_north_m;
                            double dEastDifference = itWaypointNext->m_east_m - itWaypoint->m_east_m;
                            basePositionHeadingCalculated.dGetHeading() = atan2(dEastDifference, dNorthDifference);
                            CPosition posChangeFromInitalWaypoint = (CPosition) (*itWaypointNext);
                            basePositionHeadingCalculated += posChangeFromInitalWaypoint;
                        } else {
                            double dAngleOnCircle = itWaypointNext->circleGetTurn().dGetAngle(*itWaypoint);
                            itWaypointNext->circleGetTurn().GetNewHeadingAngleAndPosition(basePositionHeadingCalculated.dGetHeading(),
                                    basePositionHeadingCalculated,
                                    dAngleOnCircle);
                            basePositionHeadingCalculated.dGetHeading() = n_Const::c_Convert::dPiO2() - basePositionHeadingCalculated.dGetHeading();
                            //need to change angle to heading
                            basePositionHeadingCalculated.dGetHeading() = n_Const::c_Convert::dPiO2() - basePositionHeadingCalculated.dGetHeading();
                            if (turnDirection == CCircle::turnClockwise) {
                                basePositionHeadingCalculated.dGetHeading() += n_Const::c_Convert::dPi();
                            }
                            basePositionHeadingCalculated += itWaypointNext->circleGetTurn();
                        }
                        bReturn = true;
                    }
                }
            } else //if((iWaypointIndexStart < (vwayGetWaypoints().size()-1))&&(iWaypointIndexStart>=0))
            {
                // no segment to extrapolate on
                bReturn = false;
            } //if((iWaypointIndexStart < (vwayGetWaypoints().size()-1))&&(iWaypointIndexStart>=0))

            return (bReturn);
        }

        int& iGetNumberAssignments() {
            return (m_iNumberAssignments);
        };

        const int& iGetNumberAssignments() const {
            return (m_iNumberAssignments);
        };

        void SetNumberAssignments(int iNumberAssignments) {
            m_iNumberAssignments = iNumberAssignments;
        };

        void UpdateAltitude(const double& dAltitude_m) {
            for (V_WAYPOINT_IT_t itWaypoint = vwayGetWaypoints().begin(); itWaypoint != vwayGetWaypoints().end(); itWaypoint++) {
                itWaypoint->m_altitude_m = dAltitude_m;
            }
        }

        void UpdateSpeed(const double& dSpeed_mps) {
            for (V_WAYPOINT_IT_t itWaypoint = vwayGetWaypoints().begin(); itWaypoint != vwayGetWaypoints().end(); itWaypoint++) {
                itWaypoint->dGetSpeed_mps() = dSpeed_mps;
            }
        }

        size_t szCalculateNumberAssignments() {
            size_t szReturn(0);
            for (V_WAYPOINT_CONST_IT_t itWaypoint = vwayGetWaypoints().begin(); itWaypoint != vwayGetWaypoints().end(); itWaypoint++) {
                szReturn += (itWaypoint->iGetObjectiveID() >= 0) ? (1) : (0);
            }
            return (szReturn);
        }

        double dCalculateFinalHeading_rad() {
            double dFinalHeading_rad(0.0);
            if (vwayGetWaypoints().size() > 1) {
                if (vwayGetWaypoints().back().circleGetTurn().turnGetTurnDirection() == CCircle::turnNone) {
#ifndef STEVETEST
                    bool bDone(false);
                    size_t szNumberWaypoints = vwayGetWaypoints().size();
                    while (!bDone) {
                        szNumberWaypoints--;
                        if (szNumberWaypoints == 0) {
                            bDone = true;
                        } else {
                            double dDistance = vwayGetWaypoints().back().relativeDistance2D_m(vwayGetWaypoints()[szNumberWaypoints]);
                            if (dDistance > 10.0) {
                                bDone = true;
                            }
                        }
                    }
                    dGetHeadingFinal() = n_Const::c_Convert::dPiO2() - vwayGetWaypoints().back().relativeAngle2D_rad(vwayGetWaypoints()[szNumberWaypoints]);
                    dFinalHeading_rad = dGetHeadingFinal();
#else    //#ifdef STEVETEST
                    V_WAYPOINT_IT_t itWaypoint = vwayGetWaypoints().end() - 2;
                    dFinalHeading_rad = n_Const::c_Convert::dPiO2() - vwayGetWaypoints().back().relativeAngle2D_rad(*itWaypoint);
#endif    //#ifdef STEVETEST
                } else {
                    //ACCOUNT FOR CURVED PATHS
                    //1) find angle of center of turn to end point
                    //2) add +/- PI/2 to 1) depending on turn direction
                    double dHeadingTemp_rad = vwayGetWaypoints().back().relativeAngle2D_rad(vwayGetWaypoints().back().circleGetTurn());
                    double dTurnDirection = (vwayGetWaypoints().back().circleGetTurn().turnGetTurnDirection() == CCircle::turnCounterclockwise) ? (1.0) :
                            (((vwayGetWaypoints().back().circleGetTurn().turnGetTurnDirection()) == CCircle::turnClockwise) ? (-1.0) : (0.0));
                    dFinalHeading_rad = n_Const::c_Convert::dPiO2() - (dHeadingTemp_rad + (dTurnDirection * n_Const::c_Convert::dPiO2()));
                } //if(circleGetTurn().turnGetTurnDirection() == turnNone)
            } //if(vwayGetWaypoints().size() > 1)

            return (dFinalHeading_rad);
        };

        int iAddWaypoint(const CWaypoint& wayWaypoint, const bool bRenumber = false) 
        {
            int iNewWaypointID = wayWaypoint.iGetID();
            
            if ((wayWaypoint.iGetObjectiveID() >= 0)&&(iNewWaypointID < 0)) {
                iNewWaypointID = static_cast<int> (wayWaypoint.dwObjID_IndexToWptID(wayWaypoint.iGetObjectiveID(), iGetWaypointID_next()));
                iGetWaypointID_next()++;
            } else if (bRenumber || (iNewWaypointID < 0)) {
                iNewWaypointID = iGetWaypointID_next();
                iGetWaypointID_next()++;
            }

            //add this waypoint's ID to the last waypoint as the "next waypoint"
            if (!vwayGetWaypoints().empty()) {
                vwayGetWaypoints().back().iGetNextWaypointID() = iNewWaypointID;
            }

            vwayGetWaypoints().push_back(wayWaypoint);
            vwayGetWaypoints().back().iGetID() = iNewWaypointID;

            return (iNewWaypointID);
        }

        int iGetNumberWaypoints() {
            return (static_cast<int> (vwayGetWaypoints().size()));
        };

        int iGetNextObjectiveHandle() {
            int iReturnHandle(-1);

            for (V_WAYPOINT_IT_t itWaypoint = itGetWaypoint(iGetWaypointCurrent()); itWaypoint != itGetWaypointEnd(); itWaypoint++) {
                if (itWaypoint->iGetObjectiveID() >= 0) {
                    iReturnHandle = itWaypoint->iGetObjectiveID();
                    break;
                }
            }
            return (iReturnHandle);
        };

        int iGetLastObjectiveHandle() {
            int iReturnHandle(-1);

            if ((iGetWaypointCurrent() >= 0)&&(iGetWaypointCurrent() < static_cast<int> (vwayGetWaypoints().size()))) {
                //assume that current waypoint can contain the last Objective, e.g. could get response from operator anytime after passing waypoint before Objective waypoint
                V_WAYPOINT_IT_t itWaypoint = itGetWaypoint(iGetWaypointCurrent());
                for (; itWaypoint != itGetWaypointFirst(); itWaypoint--) {
                    if (itWaypoint->iGetObjectiveID() >= 0) {
                        iReturnHandle = itWaypoint->iGetObjectiveID();
                        break;
                    }
                }
            }
            return (iReturnHandle);
        };

        int iGetNumberObjectivesLeft() {
            int iReturnNumber(0);
            // assume that Objective at current waypoint is not one of the Objectives that are left.
            for (V_WAYPOINT_IT_t itWaypoint = itGetWaypoint(iGetWaypointCurrent() + 1); itWaypoint != itGetWaypointEnd(); itWaypoint++) {
                if (itWaypoint->iGetObjectiveID() >= 0) {
                    iReturnNumber++;
                }
            }
            return (iReturnNumber);
        };

        int iGetWaypointIndex(const int& iWaypointID) {
            //On error returns -1
            int iReturn(-1);
            int iWaypointIndex(0);

            V_WAYPOINT_IT_t itWaypoint = itGetWaypointBegin();
            for (; itWaypoint != itGetWaypointEnd(); itWaypoint++, iWaypointIndex++) {
                if (itWaypoint->iGetID() == iWaypointID) {
                    break;
                }
            }
            if (itWaypoint != itGetWaypointEnd()) {
                iReturn = iWaypointIndex;
            }
            return (iReturn);
        }

        V_WAYPOINT_IT_t itGetWaypoint(int iIndex) {
            assert(static_cast<int> (vwayGetWaypoints().size()) > iIndex);
            return (vwayGetWaypoints().begin() + iIndex);
        };
        //    const CWaypoint itGetWaypoint(int iIndex) const {return(vwayGetWaypoints().begin() + iIndex);};

        V_WAYPOINT_IT_t itGetObjectiveWaypoint(const int& iObjectiveID) {
            V_WAYPOINT_IT_t itReturnWaypoint = vwayGetWaypoints().begin();
            for (; itReturnWaypoint != vwayGetWaypoints().end(); itReturnWaypoint++) {
                if (iObjectiveID == itReturnWaypoint->iGetObjectiveID()) {
                    break;
                }
            }
            return (itReturnWaypoint);
        }

        //accessors

        V_WAYPOINT_t& vwayGetWaypoints() {
            return (m_wayPoints);
        };

        const V_WAYPOINT_t& vwayGetWaypoints()const {
            return (m_wayPoints);
        };

        const CWaypoint& wayGetWaypoint(int iIndex) const {
            return (vwayGetWaypoints()[iIndex]);
        };

        CWaypoint& wayGetWaypoint(int iIndex) {
            return (vwayGetWaypoints()[iIndex]);
        };

        V_WAYPOINT_CONST_IT_t itGetWaypointFirst() const {
            return (vwayGetWaypoints().begin());
        };

        V_WAYPOINT_IT_t itGetWaypointFirst() {
            return (vwayGetWaypoints().begin());
        };

        V_WAYPOINT_CONST_IT_t itGetWaypointBegin() const {
            return (vwayGetWaypoints().begin());
        };

        V_WAYPOINT_IT_t itGetWaypointBegin() {
            return (vwayGetWaypoints().begin());
        };

        V_WAYPOINT_CONST_IT_t itGetWaypointEnd() const {
            return (vwayGetWaypoints().end());
        };

        V_WAYPOINT_IT_t itGetWaypointEnd() {
            return (vwayGetWaypoints().end());
        };

        const CWaypoint& wayGetWaypointLast() const {
            return (vwayGetWaypoints().back());
        };

        CWaypoint& wayGetWaypointLast() {
            return (vwayGetWaypoints().back());
        };

        const CPosition& posGetPositionAssignedLast() const {
            return (wayGetWaypointLast());
        };

        CPosition& posGetPositionAssignedLast() {
            return (wayGetWaypointLast());
        };

        void operator +=(const CAssignment& rhs) {
            for (V_WAYPOINT_CONST_IT_t itWaypoint = rhs.itGetWaypointFirst(); itWaypoint != rhs.itGetWaypointEnd(); itWaypoint++) {
                iAddWaypoint(*itWaypoint, true);
            }
            SetNumberAssignments(rhs.iGetNumberAssignments());
            SetHeadingFinal(rhs.dGetHeadingFinal());
        }

        double& dGetHeadingFinal() {
            return (m_dHeadingFinal_rad);
        };

        const double& dGetHeadingFinal() const {
            return (m_dHeadingFinal_rad);
        };

        void SetHeadingFinal(double dHeadingFinal_rad) {
            m_dHeadingFinal_rad = dHeadingFinal_rad;
        };

        const double& dGetDistancePrevious() const {
            return (m_dDistanceTotalPrevious_m);
        };

        double& dGetDistancePrevious() {
            return (m_dDistanceTotalPrevious_m);
        };

        double& dGetDistanceTemp() {
            return (m_dDistanceTotalTemp_m);
        };

        const double& dGetDistanceTemp() const {
            return (m_dDistanceTotalTemp_m);
        };

        int& iGetWaypointCurrent() {
            return (m_iWaypointCurrent);
        };

        const int& iGetWaypointCurrent() const {
            return (m_iWaypointCurrent);
        };

        V_WAYPOINT_IT_t itGetWaypointCurrent() {
            return (vwayGetWaypoints().begin() + iGetWaypointCurrent());
        };
        //    const CWaypoint& itGetWaypointCurrent() const {return(vwayGetWaypoints().begin() + iGetWaypointCurrent());};

        void EraseWaypoints(int iIndex1, int iIndex2) {
            vwayGetWaypoints().erase(itGetWaypoint(iIndex1), itGetWaypoint(iIndex2));
        };

        void EraseWaypoints(int iIndex) {
            vwayGetWaypoints().erase(itGetWaypoint(iIndex), itGetWaypointEnd());
        };

        V_TASKASSIGNMENT_t& vtaskGetAssignments() {
            return (m_vtaskAssignments);
        };

        const V_TASKASSIGNMENT_t& vtaskGetAssignments()const {
            return (m_vtaskAssignments);
        };

        int& iGetLastTaskID() {
            return (m_iLastTaskID);
        };

        const int& iGetLastTaskID() const {
            return (m_iLastTaskID);
        };

        int& iGetWaypointID_next() {
            return (m_iWaypointID_next);
        };

        const int& iGetWaypointID_next() const {
            return (m_iWaypointID_next);
        };

        double& dGetDistanceAllocatedForAssignedTasks_m() {
            return (m_dDistanceAllocatedForAssignedTasks_m);
        };

        const double& dGetDistanceAllocatedForAssignedTasks_m() const {
            return (m_dDistanceAllocatedForAssignedTasks_m);
        };

        double& dGetMinimumWaypointSeparation_m() {
            return (m_dMinimumWaypointSeparation_m);
        };

        const double& dGetMinimumWaypointSeparation_m()const {
            return (m_dMinimumWaypointSeparation_m);
        };

        int& iGetMaximumNumberWaypoints() {
            return (m_iMaximumNumberWaypoints);
        };

        const int& iGetMaximumNumberWaypoints() const {
            return (m_iMaximumNumberWaypoints);
        };

        int& iGetMinimumNumberWaypointsForTurn() {
            return (m_iMinimumNumberWaypointsForTurn);
        };

        const int& iGetMinimumNumberWaypointsForTurn() const {
            return (m_iMinimumNumberWaypointsForTurn);
        };

        double& dGetMinimumAssignmentSeparation_m() {
            return (m_dMinimumAssignmentSeparation_m);
        };

        const double& dGetMinimumAssignmentSeparation_m()const {
            return (m_dMinimumAssignmentSeparation_m);
        };

        double& dGetNewAssignmentOnsetDelay_s() {
            return (m_dNewAssignmentOnsetDelay_s);
        };

        const double& dGetNewAssignmentOnsetDelay_s()const {
            return (m_dNewAssignmentOnsetDelay_s);
        };

        double& dGetDangerDistance() {
            return m_dDangerDistance;
        };

        const double& dGetDangerDistance() const {
            return m_dDangerDistance;
        };

    protected:
        int m_iWaypointCurrent;

        V_WAYPOINT_t m_wayPoints;
        int m_iNumberAssignments;
        double m_dHeadingFinal_rad;
        double m_dDistanceTotalPrevious_m;
        double m_dDistanceTotalTemp_m; //this is used when a distance approximation is being applied to the total distance

        V_TASKASSIGNMENT_t m_vtaskAssignments;

        int m_iLastTaskID; //this is initialy set to the vehicle ID and then to the ID of each task accomplished (used during planning)

        int m_iWaypointID_next;

        double m_dDistanceAllocatedForAssignedTasks_m;
        double m_dMinimumWaypointSeparation_m;
        int m_iMaximumNumberWaypoints;
        int m_iMinimumNumberWaypointsForTurn; //Minimum Number of Waypoints per complete turn
        double m_dMinimumAssignmentSeparation_m; //this is the minimum distance between assignments
        double m_dNewAssignmentOnsetDelay_s; //this is the time to allow the vehicle to follow its current path before starting a new assignmnet, can be different than the distance
        double m_dDangerDistance; //this if for collision avoidance

    };


}; //namespace n_FrameworkLib


#endif // !defined(AFX_ASSIGNMENT_H__CA36AC9A_0A3D_4110_9E0F_7BA1B4C76258__INCLUDED_)
