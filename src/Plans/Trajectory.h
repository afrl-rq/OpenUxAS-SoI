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
// Trajectory.h: interface for the CTrajectory class.
//
//////////////////////////////////////////////////////////////////////

#if !defined(AFX_TRAJECTORY_H__CEA000CF_335F_408A_93A7_F7E16DF6EDFE__INCLUDED_)
#define AFX_TRAJECTORY_H__CEA000CF_335F_408A_93A7_F7E16DF6EDFE__INCLUDED_

#if _MSC_VER > 1000
#pragma once
#endif // _MSC_VER > 1000

//#include "GlobalDefines.h"
#include "Circle.h"
#include "Assignment.h"
#include "TrajectoryParameters.h"

namespace n_FrameworkLib
{


class CTrajectory  
{
public:    //enumerations
    enum enError
    {
        errorNone,
        errorWrongDirectionsForTangent,
        errorTotal
    };
public:    //typedefs

    typedef CWaypoint::V_WAYPOINT_t V_WAYPOINT_t;
    typedef CWaypoint::V_WAYPOINT_IT_t V_WAYPOINT_IT_t;
    typedef CWaypoint::V_WAYPOINT_CONST_IT_t V_WAYPOINT_CONST_IT_t;
public:    //constructors/destructors
    CTrajectory()
        :
            m_dAngleLoiterIncrement_rad(n_Const::c_Convert::dPiO2())
    {};
            virtual ~CTrajectory(){};

public: //member functions
    void vRound(double& rdNumber,const double dDecimalPlace)
    {
        // rounds rdNumber to the dDecimalPlace decimal place.
        // i.e. vRound(123456.123456,1e-2) => 123456.12 and vRound(123456.123456,1e2) => 123500.00
        rdNumber = floor(rdNumber/dDecimalPlace + 0.5)*dDecimalPlace;
    };
    
    void AddWaypointsForTurn(CPosition& posStart,
                                    const CPosition& posEnd,
                                    const double& dArcLength,
                                    CPosition& posCenter,
                                    const double& dRadius,
                                    const CCircle::enTurnDirection_t& turnDirection,
                                    const double& bMinimumSeparation,
                                    V_WAYPOINT_t& vWaypoints,
                                    CAssignment& cAssignment);
    
    double dMinimumDistance(CTrajectoryParameters& cTrajectoryParameters);

    void CompensateEndPointsForWind(CTrajectoryParameters& cTrajectoryParameters,V_TRAJECTORY_PARAMETERS_END_t& vParametersEnd);

    double dCalculateTrajectoryDubins(CAssignment& assignMinimum,
                                      const CPosition& pointOrign,const double& dHeadingOrigin_rad,
                                      const CPosition& pointDestination,double& dHeadingDestination_rad,
                                      const double& dTurnRadius_m,
                                      const double& dCommandSpeed_vps,
                                      const double& dMinimumWaypointSeparation_m,
                                      const double& dObjectID);

protected: //member functions
    double dMinimumDistanceEuclidean(CTrajectoryParameters& cTrajectoryParameters);
    double dMinimumDistanceDubins(CTrajectoryParameters& cTrajectoryParameters,V_TRAJECTORY_PARAMETERS_END_t& vParametersEnd);
    double dMinimumDistanceMAVWind(CAssignment& assignMinimum,CTrajectoryParameters& cTrajectoryParameters,
                                    CTrajectoryParametersEnd& trjParametersEnd,CHeadingParameters& rHeadingParameters);

    void CalculateTaskHeading(CTrajectoryParameters& cTrajectoryParameters);
    double dLengthenPath(CTrajectoryParameters& cTrajectoryParameters,
                            double dMinTimeToLengthen_s,CAssignment& assignMinimum);

    std::vector<std::vector<double>> FindLimitTurn(double* Waypoint1,double* Waypoint2,double alpha,double minStep);
    std::vector<std::vector<double>> FindPathBetweenTurns(std::vector<std::vector<double>> Turn1,std::vector<std::vector<double>> Turn2,double LengthFirstSegment,double RegularStep, 
                                       double MaxDirChange,double AirSpeed,double* Vwind,double& TimePath,bool& Found);
    bool isStepFeasible(double Dir,std::vector<double> A,std::vector<double> Aroot,std::vector<double> B,std::vector<double> Broot,double alpha);

    size_t szMinimumDistanceCircle(CPosition posBegin,CPosition posEnd,
                                CCircle& circleFirst,CCircle& circleSecond,
                                CAssignment& rassignAssignment,
                                        const double& dCommandSpeed_mps,
                                        const double& dMinimumWaypointSeparation_m);

    size_t szMinimumDistanceTurnTurnTurn(CPosition posBegin,CPosition posEnd,
                                        CCircle& circleFirst,CCircle& circleSecond,CAssignment& rassignAssignment,
                                        const double& dCommandSpeed_mps,
                                        const double& dMinimumWaypointSeparation_m);


    void AddWaypointsForTurn(CPosition& posStart,
                                const CPosition& posEnd,
                                const double& dArcLength,
                                CPosition& posCenter,
                                const double& dRadius,
                                const CCircle::enTurnDirection_t& turnDirection,
                                const double& bMinimumSeparation,
                                const double& dCommandSpeed_mps,
                                CAssignment& cAssignment);
public: //accessor functions
    const double& dGetAngleLoiterIncrement_rad()const{return(m_dAngleLoiterIncrement_rad);};

protected: //member storage
    const double m_dAngleLoiterIncrement_rad;
};

};      //namespace n_FrameworkLib

#endif // !defined(AFX_TRAJECTORY_H__CEA000CF_335F_408A_93A7_F7E16DF6EDFE__INCLUDED_)
