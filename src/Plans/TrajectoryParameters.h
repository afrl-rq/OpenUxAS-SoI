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
// TrajectoryParameters.h
//
//////////////////////////////////////////////////////////////////////

#if !defined(TRAJECTORYPARAMETERS__INCLUDED_)
#define TRAJECTORYPARAMETERS__INCLUDED_

#if _MSC_VER > 1000
#pragma once
#endif // _MSC_VER > 1000


//#include "GlobalDefines.h"
#include "HeadingParameters.h"
#include "BaseObject.h"
#include "Waypoint.h"

namespace n_FrameworkLib
{


class CTrajectoryParametersEnd: public CBaseObject
{

public:    //CONSTRUCTOR/DESTRUCTORS/OPERATOR=
    CTrajectoryParametersEnd(){};

    ~CTrajectoryParametersEnd(){};

    CTrajectoryParametersEnd(const CTrajectoryParametersEnd& rhs)
    {
        operator =(rhs);
    }

    void operator =(const CTrajectoryParametersEnd& rhs)
    {
        CBaseObject::operator =(rhs);
        waytypGetFinal() = rhs.waytypGetFinal();
        vGetHeadingParameters() = rhs.vGetHeadingParameters();
        dGetStandOffNoHeadings_m() = rhs.dGetStandOffNoHeadings_m();
    }

public:    //ACCESSORS
    CWaypoint::n_enWaypointType_t& waytypGetFinal(){return(m_waytypFinal);};
    const CWaypoint::n_enWaypointType_t& waytypGetFinal()const{return(m_waytypFinal);};

    V_HEADING_PARAMETERS_t& vGetHeadingParameters(){return(m_vHeadingParameters);};
    const V_HEADING_PARAMETERS_t& vGetHeadingParameters()const{return(m_vHeadingParameters);};

    double& dGetStandOffNoHeadings_m(){return(m_dStandOffNoHeadings_m);};
    const double& dGetStandOffNoHeadings_m()const{return(m_dStandOffNoHeadings_m);};


protected:    //STORAGE
    CWaypoint::n_enWaypointType_t m_waytypFinal{CWaypoint::waytypeObjective};    //type to use for the final waypoint
    V_HEADING_PARAMETERS_t m_vHeadingParameters;    // this is a vector of possible [headings,standoffs,free-to-turn] choices for the endpoint 
    double m_dStandOffNoHeadings_m{0.0};    // this is only used to pass in a required stand-off when there is no heading requirement. (Only used if m_vHeadingParameters is empty)

};

class CTrajectoryParameters
{
public:
    enum enPathType_t 
    {
        pathEuclidean,
        pathTurnStraightTurn,
        pathDubinMAVWind,
        pathOptimalMAVWind,
        pathOptimalMAVWindNoMovedObjectives,
        pathNumber,
    };

    
public:    //CONSTRUCTOR/DESTRUCTORS/OPERATOR=
    CTrajectoryParameters(){};

    ~CTrajectoryParameters(){};

    CTrajectoryParameters(const CTrajectoryParameters& rhs)
    {
        operator =(rhs);
    }

    void operator =(const CTrajectoryParameters& rhs)
    {
        // inputs:
        trjGetParametersEnd() = rhs.trjGetParametersEnd();
        pathGetType() = rhs.pathGetType();
        dGetMinimumTime_s() = rhs.dGetMinimumTime_s();
        dGetWindHeadingFrom_rad() = rhs.dGetWindHeadingFrom_rad();
        dGetWindSpeed_mps() = rhs.dGetWindSpeed_mps();
        bGetLengthenPath() = rhs.bGetLengthenPath();
        dGetSensorAzimuth_rad() = rhs.dGetSensorAzimuth_rad();
        dGetSensorLeadingEdge_m() = rhs.dGetSensorLeadingEdge_m();
        dGetSensorTrailingEdge_m() = rhs.dGetSensorTrailingEdge_m();
        dGetSensorCenter_m() = rhs.dGetSensorCenter_m();
        bobjGetStart() = rhs.bobjGetStart();
        dGetSpeed_mps() = rhs.dGetSpeed_mps();
        dGetAltitude_m() = rhs.dGetAltitude_m();
        dGetTurnRadius_m() = rhs.dGetTurnRadius_m();
        dGetWaypointSeparationMin_m() = rhs.dGetWaypointSeparationMin_m();

        // outputs:
        vGetWaypoints() = rhs.vGetWaypoints();
        dGetHeadingFinal_rad() = rhs.dGetHeadingFinal_rad();
        dGetDistancePath_m() = rhs.dGetDistancePath_m();
        trjGetParametersEndFinal() = rhs.trjGetParametersEndFinal();
    }

public:    //ACCESSORS


// inputs:
    CTrajectoryParametersEnd& trjGetParametersEnd(){return(m_trjParametersEnd);};
    const CTrajectoryParametersEnd& trjGetParametersEnd()const{return(m_trjParametersEnd);};

    enPathType_t& pathGetType(){return(m_pathType);};
    const enPathType_t& pathGetType()const{return(m_pathType);};

    double& dGetMinimumTime_s(){return(m_dMinimumTime_s);};
    const double& dGetMinimumTime_s()const{return(m_dMinimumTime_s);};


    double& dGetWindHeadingFrom_rad(){return(m_dWindDirectionFrom_rad);};
    const double& dGetWindHeadingFrom_rad()const{return(m_dWindDirectionFrom_rad);};

    double& dGetWindSpeed_mps(){return(m_windSpeed_mps);};
    const double& dGetWindSpeed_mps()const{return(m_windSpeed_mps);};


    bool& bGetLengthenPath(){return(m_bLengthenPath);};
    const bool& bGetLengthenPath()const{return(m_bLengthenPath);};

    double& dGetSensorAzimuth_rad(){return(m_dSensorAzimuth_rad);};
    const double& dGetSensorAzimuth_rad()const{return(m_dSensorAzimuth_rad);};

    double& dGetSensorLeadingEdge_m(){return(m_dSensorLeadingEdge_m);};
    const double& dGetSensorLeadingEdge_m()const{return(m_dSensorLeadingEdge_m);};

    double& dGetSensorTrailingEdge_m(){return(m_dSensorTrailingEdge_m);};
    const double& dGetSensorTrailingEdge_m()const{return(m_dSensorTrailingEdge_m);};

    double& dGetSensorCenter_m(){return(m_dSensorCenter_m);};
    const double& dGetSensorCenter_m()const{return(m_dSensorCenter_m);};


    CBaseObject& bobjGetStart(){return(m_bobjStart);};
    const CBaseObject& bobjGetStart()const{return(m_bobjStart);};

    double& dGetSpeed_mps(){return(m_speed_m);};
    const double& dGetSpeed_mps()const{return(m_speed_m);};

    double& dGetAltitude_m(){return(m_dAltitude_m);};
    const double& dGetAltitude_m()const{return(m_dAltitude_m);};

    double& dGetTurnRadius_m(){return(m_dTurnRadius_m);};
    const double& dGetTurnRadius_m()const{return(m_dTurnRadius_m);};

    double& dGetWaypointSeparationMin_m(){return(m_dWaypointSeparationMin_m);};
    const double& dGetWaypointSeparationMin_m()const{return(m_dWaypointSeparationMin_m);};


// outputs:
    V_WAYPOINT_t& vGetWaypoints(){return(m_vWaypoints);};
    const V_WAYPOINT_t& vGetWaypoints()const{return(m_vWaypoints);};

    double& dGetHeadingFinal_rad(){return(m_dHeadingFinal_rad);};
    const double& dGetHeadingFinal_rad()const{return(m_dHeadingFinal_rad);};

    double& dGetDistancePath_m(){return(m_dDistancePath_m);};
    const double& dGetDistancePath_m()const{return(m_dDistancePath_m);};

    CTrajectoryParametersEnd& trjGetParametersEndFinal(){return(m_trjParametersEndFinal);};
    const CTrajectoryParametersEnd& trjGetParametersEndFinal()const{return(m_trjParametersEndFinal);};


// inputs:
    enPathType_t m_pathType{pathTurnStraightTurn};    // type of path to construct
    double m_dMinimumTime_s{0.0};    //the time the vehicle takes to traverse this path must be at least this long

    double m_dWindDirectionFrom_rad{0.0};    //(from) direction of the expected average wind
    double m_windSpeed_mps{0.0};    //speed of the expected average wind

    bool m_bLengthenPath{false};    // if set to true, path will be lengthened to meet minimum ending time (m_dTimeEndingMin_s)
                                                    // if this vector is empty, the final heading is based on the optimal path
    double m_dSensorAzimuth_rad{0.0};    // relative angle of sensor to vehicle, zero out the nose, positive clockwise
    double m_dSensorLeadingEdge_m{0.0};    // distance from ground position of vehicle to sensor footprint's leading edge
    double m_dSensorTrailingEdge_m{0.0};    // distance from ground position of vehicle to sensor footprint's Trailing edge
    double m_dSensorCenter_m{0.0};    // distance from ground position of vehicle to sensor footprint's center, based on the center of the sensor's FOV

    double m_speed_m{0.0};    //planned vehicle speed.
    double m_dAltitude_m{0.0};    //planned vehicle altitude.
    double m_dTurnRadius_m{0.0};    //turn radius to use in Dubin's calculations
    double m_dWaypointSeparationMin_m{0.0};    //desired minimum distance between waypoints
    CBaseObject m_bobjStart;        //start position, heading and ID
    CTrajectoryParametersEnd m_trjParametersEnd;

// outputs:
    V_WAYPOINT_t m_vWaypoints;    //used to return the new path
    double m_dHeadingFinal_rad{0.0};    //heading of last segment of path
    double m_dDistancePath_m{-1.0};    //total distance of the path
    
    CTrajectoryParametersEnd m_trjParametersEndFinal;    // the parameters that were used in the minimum distance path
};

namespace
{
    typedef std::vector<CTrajectoryParametersEnd> V_TRAJECTORY_PARAMETERS_END_t;
    typedef std::vector<CTrajectoryParametersEnd>::iterator V_TRAJECTORY_PARAMETERS_END_IT_t;
    typedef std::vector<CTrajectoryParametersEnd>::const_iterator V_TRAJECTORY_PARAMETERS_END_CONST_IT_t;

    typedef std::vector<CTrajectoryParameters> V_TRAJECTORY_PARAMETERS_t;
    typedef std::vector<CTrajectoryParameters>::iterator V_TRAJECTORY_PARAMETERS_IT_t;
    typedef std::vector<CTrajectoryParameters>::const_iterator V_TRAJECTORY_PARAMETERS_CONST_IT_t;
}

};      //namespace n_FrameworkLib


#endif // !defined(TRAJECTORYPARAMETERS__INCLUDED_)
