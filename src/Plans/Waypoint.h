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
// Waypoint.h: interface for the CWaypoint class.
//
//////////////////////////////////////////////////////////////////////

#if !defined(AFX_WAYPOINT_H__CE91A42E_2AFF_46F1_9D41_15AD11E2A6D6__INCLUDED_)
#define AFX_WAYPOINT_H__CE91A42E_2AFF_46F1_9D41_15AD11E2A6D6__INCLUDED_

#if _MSC_VER > 1000
#pragma once
#endif // _MSC_VER > 1000


#include <limits>
using namespace std;

#include <memory>    //std::shared_ptr
#include "afrl/cmasi/Waypoint.h"


//#include "GlobalDefines.h"
#include "UnitConversions.h"
#include "Position.h"
#include "Circle.h"

#include <ostream>
//using std::ostream;
#include <map>

// TODO: remove all waypoint mangling
#define TASK_ID_MULTIPLIER 10000    // use this to make the waypoint index visible in the mangeled id (up to 9999 waypoints)

namespace n_FrameworkLib
{
    
    typedef std::shared_ptr<afrl::cmasi::Waypoint> PTR_CMASI_WAYPOINT_t;

class CWaypoint;

typedef vector<CWaypoint> V_WAYPOINT_t;
typedef V_WAYPOINT_t::iterator V_WAYPOINT_IT_t;
typedef V_WAYPOINT_t::const_iterator V_WAYPOINT_CONST_IT_t;
typedef V_WAYPOINT_t::reverse_iterator V_WAYPOINT_REVERSE_IT_t;

typedef map<int,CWaypoint> M_I_WAYPOINT_t;
typedef map<int,CWaypoint>::iterator M_I_WAYPOINT_IT_t;
typedef map<int,CWaypoint>::const_iterator M_I_WAYPOINT_CONST_IT_t;

class CDataPoint : public CPosition
{
public:    //constructors
    CDataPoint(double reTime=0.0,
                    double reNorth=0.0,double reEast=0.0,double reAltitude=0.0,
                    double rePhi=0.0,double reTheta=0.0,double rePsi=0.0,
                    double reVelocity=50.0)
        :   CPosition(reNorth,reEast,reAltitude),
			m_reTime_sec(reTime),
            m_rePhi_deg(rePhi),m_reTheta_deg(reTheta),m_rePsi_deg(rePsi),
            m_speed_mps(reVelocity)
    {};
    virtual ~CDataPoint(){};

    //copy constructor
    CDataPoint(const CDataPoint& rhs)
    {
        reGetTime() = rhs.reGetTime();
        m_north_m = rhs.m_north_m;
        m_east_m = rhs.m_east_m;
        m_altitude_m = rhs.m_altitude_m;
        reGetPhi() = rhs.reGetPhi();
        reGetTheta() = rhs.reGetTheta();
        reGetPsi() = rhs.reGetPsi();
        reGetVelocity() = rhs.reGetVelocity();
    };

public:    //operator overrides
    void operator =(const CDataPoint& rhs)
    {
        reGetTime() = rhs.reGetTime();
        m_north_m = rhs.m_north_m;
        m_east_m = rhs.m_east_m;
        m_altitude_m = rhs.m_altitude_m;
        reGetPhi() = rhs.reGetPhi();
        reGetTheta() = rhs.reGetTheta();
        reGetPsi() = rhs.reGetPsi();
        reGetVelocity() = rhs.reGetVelocity();
    };

public:    //accessors

    double& reGetTime(){return(m_reTime_sec);};
    const double& reGetTime()const{return(m_reTime_sec);};

//    double& m_north_m{return(m_reNorth_m);};
//    const double& m_north_mconst{return(m_reNorth_m);};

//    double& m_east_m{return(m_reEast_m);};
//    const double& m_east_mconst{return(m_reEast_m);};

//    double& reGetAltitude(){return(m_reAltitude_m);};
//    const double& reGetAltitude()const{return(m_reAltitude_m);};

    double& reGetPhi(){return(m_rePhi_deg);};
    const double& reGetPhi()const{return(m_rePhi_deg);};

    double& reGetTheta(){return(m_reTheta_deg);};
    const double& reGetTheta()const{return(m_reTheta_deg);};

    double& reGetPsi(){return(m_rePsi_deg);};
    const double& reGetPsi()const{return(m_rePsi_deg);};

    double& reGetVelocity(){return(m_speed_mps);};
    const double& reGetVelocity()const{return(m_speed_mps);};

protected: // member storage
    double m_reTime_sec;
//    double m_reNorth_m;
//    double m_reEast_m;
//    double m_reAltitude_m;
    double m_rePhi_deg;
    double m_reTheta_deg;
    double m_rePsi_deg;
    double m_speed_mps;
};

class CWaypointSmall : public CPosition
{
public:    //constructors
    CWaypointSmall(double reNorth=0.0,double reEast=0.0,double reAltitude=0.0,const CPosition::enPositionUnits& postionUnits=CPosition::unitsFeet)
    {
        switch(postionUnits)
        {
        default:
        case CPosition::unitsFeet:
            m_north_m = reNorth;
            m_east_m = reEast;
            m_altitude_m = reAltitude;
            break;
        case unitsMeters:
            m_north_m = reNorth;
            m_east_m = reEast;
            m_altitude_m = reAltitude;
            break;
#ifdef USE_LAT_LONGS_FROM_WAYPOINTS
        case unitsLatitudeLongitude_deg:    //fall through for conversion
            reNorth *= n_Const::c_Convert::dDegreesToRadians();
            reEast *= n_Const::c_Convert::dDegreesToRadians();
        case unitsLatitudeLongitude_rad:
            if(!cGetUnitConversions().bGetInitialized())
            {
                cGetUnitConversions().Initilize(reNorth,reEast);
            }
            m_north_m = cGetUnitConversions().dConvertLatitudeToNorth_m(reNorth);
            m_east_m = cGetUnitConversions().dConvertLongitudeToEast_m(reEast);
            m_altitude_m = reAltitude;    //assume in feet
            break;
#endif    //#ifdef USE_LAT_LONGS_FROM_WAYPOINTS
        }
    };


    CWaypointSmall(const CPosition& rhs)
        : CPosition(rhs)
    {};

    virtual ~CWaypointSmall(){};

    //copy constructor
    CWaypointSmall(const CWaypointSmall& rhs)
        : CPosition(rhs)
    {};

public:    //operator overrides
    void operator =(const CWaypointSmall& rhs)
    {
        m_north_m = rhs.m_north_m;
        m_east_m = rhs.m_east_m;
        m_altitude_m = rhs.m_altitude_m;
    };

    void operator =(const CPosition& rhs)
    {
        m_north_m = rhs.m_north_m;
        m_east_m = rhs.m_east_m;
        m_altitude_m = rhs.m_altitude_m;
    };
public:    //member functions

    double reRelativeDistance2D(const CWaypointSmall& wayPoint )
    {
        using namespace std;

        // returns the distance between this waypoint and another
        double dX = m_north_m - wayPoint.m_north_m; 
        double dY = m_east_m - wayPoint.m_east_m; 

        return(sqrt((dX*dX) + (dY*dY)));
    };


#ifdef USE_LAT_LONGS_FROM_WAYPOINTS
    //when using the Algorithm class, it has it's own copy of cGetUnitConversions(), so these can be cofused with those.
    double m_latitude_rad
    {
        return(cGetUnitConversions().dConvertNorth_mToLatitude_rad(m_north_m));
    };
    double m_longitude_rad
    {
        return(cGetUnitConversions().dConvertEast_mToLongitude_rad(m_east_m));
    };

public:    //accessors
    uxas::common::utilities::CUnitConversions& cGetUnitConversions(){return(m_UnitConversions);};
    const uxas::common::utilities::CUnitConversions& cGetUnitConversions()const{return(m_UnitConversions);};

protected: // member storage
    static uxas::common::utilities::CUnitConversions m_UnitConversions;
#endif    //#ifdef USE_LAT_LONGS_FROM_WAYPOINTS
};


class CWaypoint : public CWaypointSmall 
{
public:
    enum enEntries    //used to keep track of number of entries
    {
        entryPositionNorth,
        entryPositionEast,
        entryPositionAltitude,
        entryTurnCenterNorth,
        entryTurnCenterEast,
        entrySegmentLength,
        entryVelocity,
        entryTurnDirection,
        entryType,
        entryObjectiveHandle,
        entryObjectiveDesiredDirection_rad,
        entryObjectiveDesiredStandOff_m,
        entryTotal,
    };
    enum enSensorStates
    {
        sstateOff,
        sstateFrontCamera,
        ssStateSideCamera,
        sstateTotal
    };
    enum n_enWaypointType_t 
    {
        waytypeSearch=1,
        waytypeEnroute,
        waytypeClassify,
        waytypeAttack,
        waytypeVerify,
        waytypeStartPoint,
        waytypeEndPoint,
        waytypeStandOff,
        waytypeSensorOnObjective,
        waytypeRevisitBegin,
        waytypeRevisitEnd,
        waytypeStochasticBingoPoint,
        waytypeObjective,
        waytypeLoiter,
        waytypeNumberEntries,
        waytypeEndTask=100,
        waytypeEndTaskReplan=200,
        waytypeQualifierMultiple
    };
    enum n_enTaskType_t 
    {
        taskAnotherLook_01,
        taskAnotherLook_02,
        taskLoiter,
        taskObjective,
        taskSearch,
        taskClassify,
        taskAttack,
        taskVerify,
        taskFinished,
        taskUnknown,
        taskNumberEntries
    };

public:
    typedef numeric_limits<double> NUMERIC_LIMITS_double;

    typedef vector<CWaypoint> V_WAYPOINT_t;
    typedef V_WAYPOINT_t::iterator V_WAYPOINT_IT_t;
    typedef V_WAYPOINT_t::const_iterator V_WAYPOINT_CONST_IT_t;

public:    //constructors

    CWaypoint(    double dPositionNorth_m,
                double dPositionEast_m,
                double dAltitude_m,
                double dVelocity_mpersec,
                bool    bMachCommandFlag,
                double SegmentLength_m=0.0,
                double dTurnCenterNorth_m=(std::numeric_limits<double>::max)(),
                double dTurnCenterEast_m=(std::numeric_limits<double>::max)(),
                double dTurnRadius_m=(std::numeric_limits<double>::max)(),
                CCircle::enTurnDirection_t turnDirection=CCircle::turnNone,
                n_enWaypointType_t typeWaypoint=waytypeEnroute,
                int iObjectiveID=-1,
                double tstart=0,
                double tend=0
            )
        :CWaypointSmall(dPositionNorth_m,dPositionEast_m,dAltitude_m),
		 m_iID(-1),
		 m_iNextWaypointID(-1),
         m_speed_mps(dVelocity_mpersec),
         m_bMachCommandFlag(bMachCommandFlag),
         m_dSegmentLength_m(SegmentLength_m),
         m_circleTurn(dTurnCenterNorth_m,dTurnCenterEast_m,dTurnRadius_m,turnDirection),
         m_typeWaypoint(typeWaypoint),
         m_iObjectiveID(iObjectiveID),
         m_dObjectiveDesiredDirection_rad(0.0),
         m_dObjectiveDesiredStandOff_m(0.0),
         m_bResetVehiclePosition(false),
         m_sstateSensorState(sstateFrontCamera),
         m_reSegmentTime_sec(0.0),
         m_tstart(tstart),
         m_tend(tend),
         m_dLoiterRadius_m(-1.0),    //invalid
         m_iLoiterDuration_s(0),
         m_bDoNotRemove(false),
         m_ptr_CMASI_Waypoint(new afrl::cmasi::Waypoint())
    {
    };

    CWaypoint(const CPosition::enPositionUnits& postionUnits,
                double dNorth,double dEast,double dAltitude,double dVelocity_mpersec
            )
        :CWaypointSmall(dNorth,dEast,dAltitude,postionUnits),
		 m_iID(-1),
		 m_iNextWaypointID(-1),
         m_speed_mps(dVelocity_mpersec),
         m_dSegmentLength_m(0.0),
         m_circleTurn((std::numeric_limits<double>::max)(),(std::numeric_limits<double>::max)(),(std::numeric_limits<double>::max)(),CCircle::turnNone),
         m_typeWaypoint(waytypeEnroute),
         m_iObjectiveID(-1),
         m_dObjectiveDesiredDirection_rad(0.0),
         m_dObjectiveDesiredStandOff_m(0.0),
         m_bResetVehiclePosition(false),
         m_sstateSensorState(sstateFrontCamera),
         m_reSegmentTime_sec(0.0),
         m_tstart(0.0),
         m_tend(0.0),
         m_dLoiterRadius_m(-1.0),    //invalid
         m_iLoiterDuration_s(0),
         m_bDoNotRemove(false),
         m_ptr_CMASI_Waypoint(new afrl::cmasi::Waypoint())

    {
    };

    CWaypoint()
        :CWaypointSmall(0.0,0.0,0.0),
		 m_iID(-1),
		 m_iNextWaypointID(-1),
         m_speed_mps(0.0),
         m_dSegmentLength_m(0.0),
         m_circleTurn((std::numeric_limits<double>::max)(),(std::numeric_limits<double>::max)(),(std::numeric_limits<double>::max)(),CCircle::turnNone),
         m_typeWaypoint(waytypeEnroute),
         m_iObjectiveID(-1),
         m_dObjectiveDesiredDirection_rad(0.0),
         m_dObjectiveDesiredStandOff_m(0.0),
         m_bResetVehiclePosition(false),
         m_sstateSensorState(sstateFrontCamera),
         m_reSegmentTime_sec(0.0),
         m_tstart(0.0),
         m_tend(0.0),
         m_dLoiterRadius_m(-1.0),    //invalid
         m_iLoiterDuration_s(0),
         m_bDoNotRemove(false),
         m_ptr_CMASI_Waypoint(new afrl::cmasi::Waypoint())

    {
    };

    CWaypoint(double reNorth,double reEast,double reAltitude=0.0,const CPosition::enPositionUnits& postionUnits=CPosition::unitsFeet)
        :CWaypointSmall(reNorth,reEast,reAltitude,postionUnits),
		 m_iID(-1),
		 m_iNextWaypointID(-1),
         m_speed_mps(0.0),
         m_dSegmentLength_m(0.0),
         m_circleTurn((std::numeric_limits<double>::max)(),(std::numeric_limits<double>::max)(),(std::numeric_limits<double>::max)(),CCircle::turnNone),
         m_typeWaypoint(waytypeEnroute),
         m_iObjectiveID(-1),
         m_dObjectiveDesiredDirection_rad(0.0),
         m_dObjectiveDesiredStandOff_m(0.0),
         m_bResetVehiclePosition(false),
         m_sstateSensorState(sstateFrontCamera),
         m_reSegmentTime_sec(0.0),
         m_tstart(0.0),
         m_tend(0.0),
         m_dLoiterRadius_m(-1.0),    //invalid
         m_iLoiterDuration_s(0),
         m_bDoNotRemove(false),
         m_ptr_CMASI_Waypoint(new afrl::cmasi::Waypoint())

    {
    };

    CWaypoint(CPosition& posPosition,
                    double dMachCommand=0.0,
                    bool bMachCommandFlag=true,
                    double dSegmentLength_m=0,
                    double dTurnCenterX_m=(std::numeric_limits<double>::max)(),
                    double dTurnCenterY_m=(std::numeric_limits<double>::max)(),
                    double dTurnRadius_m=(std::numeric_limits<double>::max)(),
                    CCircle::enTurnDirection_t turnDirection=CCircle::turnNone,
                    n_enWaypointType_t typeWaypoint=waytypeEnroute,
                    int iObjectiveID=-1,
                    bool bResetVehiclePosition=false,
                    enSensorStates m_sstateSensorState=sstateFrontCamera,
                    double m_reSegmentTime_sec=0.0
                    ) 
    	:CWaypointSmall(posPosition),
		 m_iID(-1),
		 m_iNextWaypointID(-1),
         m_speed_mps(dMachCommand),m_bMachCommandFlag(bMachCommandFlag),
         m_dSegmentLength_m(dSegmentLength_m),
         m_circleTurn(dTurnCenterX_m,dTurnCenterY_m,dTurnRadius_m,turnDirection),
         m_typeWaypoint(typeWaypoint),
         m_iObjectiveID(iObjectiveID),
         m_dObjectiveDesiredDirection_rad(0.0),
         m_dObjectiveDesiredStandOff_m(0.0),
         m_bResetVehiclePosition(bResetVehiclePosition),
         m_sstateSensorState(sstateFrontCamera),
         m_reSegmentTime_sec(0.0),
         m_tstart(0.0),
         m_tend(0.0),
         m_dLoiterRadius_m(-1.0),    //invalid
         m_iLoiterDuration_s(0),
         m_bDoNotRemove(false),
         m_ptr_CMASI_Waypoint(new afrl::cmasi::Waypoint())

    {
    };

        
    virtual ~CWaypoint()
    {
    };

    CWaypoint(const CWaypoint& rhs)
    {
        operator=(rhs);
    };

    void operator=(const CWaypoint& rhs)
    {
        CWaypointSmall::operator =(rhs);
        circleGetTurn() = rhs.circleGetTurn();
        dGetSpeed_mps() = rhs.dGetSpeed_mps();
        bGetMachCommandFlag() = rhs.bGetMachCommandFlag();
        dGetSegmentLength() = rhs.dGetSegmentLength();
        typeGetWaypoint() = rhs.typeGetWaypoint();
        iGetObjectiveID() = rhs.iGetObjectiveID();
        dGetObjectiveDesiredDirection_rad() = rhs.dGetObjectiveDesiredDirection_rad();
        dGetObjectiveDesiredStandOff_m() = rhs.dGetObjectiveDesiredStandOff_m();
        bGetResetVehiclePosition() = rhs.bGetResetVehiclePosition();
        sstateGetSensorState() = rhs.sstateGetSensorState();
        reGetSegmentTime() = rhs.reGetSegmentTime();
        iGetID() = rhs.iGetID();
        iGetNextWaypointID() = rhs.iGetNextWaypointID();
        dGetTStart() = rhs.dGetTStart();
        dGetTEnd() = rhs.dGetTEnd();
        dGetLoiterRadius_m() = rhs.dGetLoiterRadius_m();
        iGetLoiterDuration_s() = rhs.iGetLoiterDuration_s();
        bGetDoNotRemove() = rhs.bGetDoNotRemove();
                ptr_GetCMASI_Waypoint().reset(rhs.ptr_GetCMASI_Waypoint()->clone());
    };

    void operator=(const CPosition& rhs)
    {
        CWaypointSmall::operator =(rhs);
    };
    
    void osStreamWaypointHeadings(ostream &os); 
    

    bool bIsWaypointEligibleForRemoval()
    {
        bool bReturn(true);
        if(bGetDoNotRemove() || (iGetObjectiveID() > 0) || (typeGetWaypoint() == waytypeObjective))
        {
            bReturn = false;
        }

        return(bReturn);
    }

    string strGetType()
    {
        string strWaypointType("wayTypeUnknown");
        switch(typeGetWaypoint())
        {
        case waytypeSearch:
            strWaypointType = "waytypeSearch";
            break;
        case waytypeEnroute:
            strWaypointType = "waytypeEnroute";
            break;
        case waytypeClassify:
            strWaypointType = "waytypeClassify";
            break;
        case waytypeAttack:
            strWaypointType = "waytypeAttack";
            break;
        case waytypeVerify:
            strWaypointType = "waytypeVerify";
            break;
        case waytypeStartPoint:
            strWaypointType = "waytypeStartPoint";
            break;
        case waytypeEndPoint:
            strWaypointType = "waytypeEndPoint";
            break;
        case waytypeStandOff:
            strWaypointType = "waytypeStandOff";
            break;
        case waytypeSensorOnObjective:
            strWaypointType = "waytypeSensorOnObjective";
            break;
        case waytypeRevisitBegin:
            strWaypointType = "waytypeRevisitBegin";
            break;
        case waytypeRevisitEnd:
            strWaypointType = "waytypeRevisitEnd";
            break;
        case waytypeStochasticBingoPoint:
            strWaypointType = "waytypeStochasticBingoPoint";
            break;
        case waytypeLoiter:
            strWaypointType = "waytypeLoiter";
            break;
        default:
            break;
        }
        return(strWaypointType);
    }

    n_enWaypointType_t waytypConvertTaskToWaypointType(const n_enTaskType_t& taskType)
    {
        n_enWaypointType_t waytypReturn(waytypeSearch);

        switch(taskType)
        {
        default:
        case taskFinished:
            // nothing to do for this Objective
            break;
        case taskAttack:
            waytypReturn = waytypeAttack;
            break;
        case taskVerify:
            waytypReturn = waytypeVerify;
            break;
        case taskClassify:
            waytypReturn = waytypeClassify;
            break;
        }
        return(waytypReturn);
    };

    void RotateAboutOriginByHeading(const double& reDeltaHeading_rad)
    {
        //rotate this waypoint about the given point
        // heading angle is referenced from north (0.0) with a positive rotation clockwize
        double reNorthTemp = m_north_m;
        double reEastTemp = m_east_m;

        m_north_m = reNorthTemp*cos(reDeltaHeading_rad) - reEastTemp*sin(reDeltaHeading_rad);
        m_east_m = reNorthTemp*sin(reDeltaHeading_rad) + reEastTemp*cos(reDeltaHeading_rad);

        //need to rotate turn center
        if(turnGetTurnDirection() != CCircle::turnNone)
        {
            double reTurnCenterNorthTemp = dGetTurnCenterNorth();
            double reTurnCenterEastTemp = dGetTurnCenterEast();

            dGetTurnCenterNorth() = reTurnCenterNorthTemp*cos(reDeltaHeading_rad) - reTurnCenterEastTemp*sin(reDeltaHeading_rad);
            dGetTurnCenterEast() = reTurnCenterNorthTemp*sin(reDeltaHeading_rad) + reTurnCenterEastTemp*cos(reDeltaHeading_rad);
        }
    };
    void AddNorthEast(const CWaypointSmall& rhs)
    {
        m_north_m += rhs.m_north_m;
        m_east_m += rhs.m_east_m;

        //need to add to turn center
        if(turnGetTurnDirection() != CCircle::turnNone)
        {
            dGetTurnCenterNorth() += rhs.m_north_m;
            dGetTurnCenterEast() += rhs.m_east_m;
        }
    };

    const int64_t dwObjID_IndexToWptID(const int& iObjectiveID, const int& iIndex) const
    {

        int64_t dwReturn = static_cast<int64_t>((iIndex > 0) ? (iIndex) : (0));
        if (iObjectiveID >= 0)
        {
            dwReturn += static_cast<int64_t>((iObjectiveID*TASK_ID_MULTIPLIER));
        }
        return(dwReturn);
    };

    int iWptID_ToIndex(const int64_t& dwID)
    {
        int iReturn = static_cast<int>(dwID % TASK_ID_MULTIPLIER);
        return(iReturn);
    };

    int iWptID_ToObjectiveID(const int64_t& dwID)
    {
        int iReturn = static_cast<int>(dwID / TASK_ID_MULTIPLIER);
        return(iReturn);
    };


public:

    int& iGetID(){return(m_iID);};
    const int& iGetID()const{return(m_iID);};

    int& iGetNextWaypointID(){return(m_iNextWaypointID);};
    const int& iGetNextWaypointID()const{return(m_iNextWaypointID);};

    double& dGetSpeed_mps(){return(m_speed_mps);};
    const double& dGetSpeed_mps() const {return(m_speed_mps);};
    
    bool& bGetMachCommandFlag(){return(m_bMachCommandFlag);};
    const bool& bGetMachCommandFlag() const {return(m_bMachCommandFlag);};
    void SetMachCommandFlag(bool bMachCommandFlag){m_bMachCommandFlag=bMachCommandFlag;};

    double& dGetSegmentLength(){return(m_dSegmentLength_m);};
    const double& dGetSegmentLength() const {return(m_dSegmentLength_m);};
    void SetSegmentLength(double dSegmentLength){dGetSegmentLength()=dSegmentLength;};

    CCircle& circleGetTurn(){return(m_circleTurn);};
    const CCircle& circleGetTurn() const {return(m_circleTurn);};
    
    double& dGetTurnCenterNorth(){return(circleGetTurn().m_north_m);};
    const double& dGetTurnCenterNorth() const {return(circleGetTurn().m_north_m);};

    double& dGetTurnCenterEast(){return(circleGetTurn().m_east_m);};
    const double& dGetTurnCenterEast() const {return(circleGetTurn().m_east_m);};

    CCircle::enTurnDirection_t& turnGetTurnDirection(){return(circleGetTurn().turnGetTurnDirection());};
    const CCircle::enTurnDirection_t& turnGetTurnDirection()const{return(circleGetTurn().turnGetTurnDirection());};

    n_enWaypointType_t& typeGetWaypoint(){return(m_typeWaypoint);};
    const n_enWaypointType_t& typeGetWaypoint() const {return(m_typeWaypoint);};
    void SetTypeWaypoint(n_enWaypointType_t typeWaypoint){m_typeWaypoint=typeWaypoint;};

    int& iGetObjectiveID(){return(m_iObjectiveID);};
    const int& iGetObjectiveID() const {return(m_iObjectiveID);};
    void SetObjectiveHandle(int iObjectiveID){m_iObjectiveID=iObjectiveID;};

    double& dGetObjectiveDesiredDirection_rad(){return(m_dObjectiveDesiredDirection_rad);};
    const double& dGetObjectiveDesiredDirection_rad() const {return(m_dObjectiveDesiredDirection_rad);};

    double& dGetObjectiveDesiredStandOff_m(){return(m_dObjectiveDesiredStandOff_m);};
    const double& dGetObjectiveDesiredStandOff_m() const {return(m_dObjectiveDesiredStandOff_m);};

    bool& bGetResetVehiclePosition(){return(m_bResetVehiclePosition);};
    const bool& bGetResetVehiclePosition() const {return(m_bResetVehiclePosition);};
    void SetResetVehiclePosition(bool bResetVehiclePosition){m_bResetVehiclePosition=bResetVehiclePosition;};

    enSensorStates& sstateGetSensorState(){return(m_sstateSensorState);};
    const enSensorStates& sstateGetSensorState() const {return(m_sstateSensorState);};

    double& reGetSegmentTime(){return(m_reSegmentTime_sec);};
    const double& reGetSegmentTime()const{return(m_reSegmentTime_sec);};

    double& dGetTStart(){return(m_tstart);};
    const double& dGetTStart() const {return(m_tstart);};

    double& dGetTEnd(){return(m_tend);};
    const double& dGetTEnd() const {return(m_tend);};

    double& dGetLoiterRadius_m(){return(m_dLoiterRadius_m);};
    const double& dGetLoiterRadius_m() const {return(m_dLoiterRadius_m);};

    int& iGetLoiterDuration_s(){return(m_iLoiterDuration_s);};
    const int& iGetLoiterDuration_s() const {return(m_iLoiterDuration_s);};

    bool& bGetDoNotRemove(){return(m_bDoNotRemove);};
    const bool& bGetDoNotRemove() const {return(m_bDoNotRemove);};

        PTR_CMASI_WAYPOINT_t& ptr_GetCMASI_Waypoint(){return(m_ptr_CMASI_Waypoint);};
        const PTR_CMASI_WAYPOINT_t& ptr_GetCMASI_Waypoint()const{return(m_ptr_CMASI_Waypoint);};
        
protected:
    int m_iID;    //this id will be unique for every new waypoint added
    int m_iNextWaypointID;    //the it to goto after this waypoint
    double m_speed_mps;          // commanded speed
    bool m_bMachCommandFlag;
    double m_dSegmentLength_m;    //length of segment from last waypoint to this waypoint 
    CCircle m_circleTurn;    // 2D location of center of turning circle
    n_enWaypointType_t m_typeWaypoint;
    int m_iObjectiveID;        // handle of Objective at this waypoint, -1 is for no Objective
    double m_dObjectiveDesiredDirection_rad;        // desired direction to Objective at this waypoint, 0 is for no Objective
    double m_dObjectiveDesiredStandOff_m;        // desired direction to Objective at this waypoint, 0 is for no Objective
    bool m_bResetVehiclePosition;
    enSensorStates m_sstateSensorState;    //enumerated state of the sensor(s)
    double m_reSegmentTime_sec;

    double m_tstart;
    double m_tend;

    double m_dLoiterRadius_m;
    int m_iLoiterDuration_s;

    bool m_bDoNotRemove;    // if this flag is true then put this waypoint in the plan even if it is close to another

    PTR_CMASI_WAYPOINT_t m_ptr_CMASI_Waypoint;    //fisrt step: only using for passing actions to CMASI

//Added by Nicola Ceccarelli 04/05/2007
protected:
    enum enErrTimeToGo    //map the possible erros in evaluating TimeToGo
    {
        NoError,
        ZeroSpeedError, //the waypoint commanded air speed is 0
        NegativeSpeedError, //the waypoint commanded air speed is negative return INF
        WindSpeedGreaterEqualAirSpeedNoError, //Wind speed >= Air Speed but the solution is ok
        WindSpeedGreaterAirSpeedError //Wind speed >= Air Speed no solution  return INF
    };
public:
    
    double reRelativeDistance2D(const CWaypoint& wayPoint )
    {
        return(CWaypointSmall::reRelativeDistance2D(static_cast<const CWaypointSmall&>(wayPoint)));
    };
/*    double reRelativeDistance2D(const CWaypoint& wayPoint ) const
                {
        return(CWaypointSmall::reRelativeDistance2D(static_cast<const CWaypointSmall&>(wayPoint)));
                };*/
    
    enErrTimeToGo erTimeToGo(double& dTimeToGo_s,const CWaypoint& wayPoint,
                             const double& dWindDirection_NE_comingfrom_rad = 0.0,
                             const double& windSpeed_mps = 0.0
                             )//estimate the time to reach another waypoint, the speed assumed is that of the destination point 
    {    
        if (wayPoint.dGetSpeed_mps()>0)  
        {
            double SegDir=atan2(wayPoint.m_east_m-m_east_m,wayPoint.m_north_m-m_north_m);
            double alpha=SegDir-(dWindDirection_NE_comingfrom_rad-n_Const::c_Convert::dPi());
            if (wayPoint.dGetSpeed_mps()>=fabs(windSpeed_mps*sin(alpha)))
            {
                double Vg=sqrt(pow(wayPoint.dGetSpeed_mps(),2)-pow(windSpeed_mps*sin(alpha),2))+windSpeed_mps*cos(alpha);
                dTimeToGo_s=reRelativeDistance2D(wayPoint)/Vg;
                if (wayPoint.dGetSpeed_mps()>windSpeed_mps)
                    return(NoError);
                else 
                    return(WindSpeedGreaterEqualAirSpeedNoError); 
            }
            else 
            {
                dTimeToGo_s=(std::numeric_limits<double>::max)();
                return(WindSpeedGreaterAirSpeedError);
            }

        }
        else if (wayPoint.dGetSpeed_mps()==0)
        {
            dTimeToGo_s=(std::numeric_limits<double>::max)();
            return(ZeroSpeedError);
        }
        else
        {
            dTimeToGo_s=(std::numeric_limits<double>::max)();
            return(NegativeSpeedError);
        }        

    };

};


ostream &operator << (ostream &os,const CWaypoint& wayRhs);

};      //namespace n_FrameworkLib

#endif // !defined(AFX_WAYPOINT_H__CE91A42E_2AFF_46F1_9D41_15AD11E2A6D6__INCLUDED_)
