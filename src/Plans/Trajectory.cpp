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
// Trajectory.cpp: implementation of the CTrajectory class.
//
////////////////////////////////////

#include "Trajectory.h"


namespace n_FrameworkLib
{


double CTrajectory::dMinimumDistance(CTrajectoryParameters& cTrajectoryParameters)
{
    double dDistanceMinimum_m = std::numeric_limits<double>::max();    //initialize to big number, in case of failure

    V_TRAJECTORY_PARAMETERS_END_t vParametersEnd;    // used to move the end conditions based on wind values (for fixed camera look angles)

    CTrajectoryParameters::enPathType_t pathType = cTrajectoryParameters.pathGetType();
    //CTrajectoryParameters::enPathType_t pathType = CTrajectoryParameters::pathEuclidean;

    //TODO::ASSUME:: if the final point is too close, then do a Euclidean path 
    if((pathType == CTrajectoryParameters::pathEuclidean)||(cTrajectoryParameters.dGetTurnRadius_m() < 1.0))
    {
        //pathType = pathEuclidean;
        dDistanceMinimum_m = dMinimumDistanceEuclidean(cTrajectoryParameters);
    }
    else        //if((pathType == pathEuclidean)||(cTrajectoryParameters.bobjGetStart().dRelativeDistance2D(cTrajectoryParameters.posGetFinal()) < 50.0))
    {
        CalculateTaskHeading(cTrajectoryParameters);
        switch(pathType)
        {
        case CTrajectoryParameters::pathTurnStraightTurn:
        case CTrajectoryParameters::pathOptimalMAVWindNoMovedObjectives: //DO NOT Move the Objectives but calculate the path with dubins adapted to Wind
            vParametersEnd.push_back(cTrajectoryParameters.trjGetParametersEnd());    // copy used in dMinimumDistanceDubins
            dDistanceMinimum_m = dMinimumDistanceDubins(cTrajectoryParameters,vParametersEnd);
            break;
        case CTrajectoryParameters::pathOptimalMAVWind: //Move the Objectives based on wind calculate the path with dubins adapted to Wind
        case CTrajectoryParameters::pathDubinMAVWind: //Move the Objectives based on wind calculate the path with dubins
            CompensateEndPointsForWind(cTrajectoryParameters,vParametersEnd);
            dDistanceMinimum_m = dMinimumDistanceDubins(cTrajectoryParameters,vParametersEnd);
            break;
        default:
            //TODO:: ERROR:: unknown path type
            break;
        }        //switch(pathType)
    }        //if((pathType == pathEuclidean)||(cTrajectoryParameters.bobjGetStart().dRelativeDistance2D(cTrajectoryParameters.posGetFinal()) < 50.0))

    return(dDistanceMinimum_m);
}


double CTrajectory::dMinimumDistanceEuclidean(CTrajectoryParameters& cTrajectoryParameters)
{
    double dAngleRelative_rad;
    double dDistance_m = cTrajectoryParameters.bobjGetStart().relativeDistanceAngle2D_m(cTrajectoryParameters.trjGetParametersEnd(),dAngleRelative_rad);
    double dHeadingFinal_rad = n_Const::c_Convert::dPiO2() - dAngleRelative_rad;

    //////////////////////////////////////////////////////////////////////////////////////
    // lengthen completion times (distance) if necessary
    ////////////////////////////////////////////////////////////////////////////////////////
    double dMinimumPathLength = cTrajectoryParameters.dGetMinimumTime_s()*cTrajectoryParameters.dGetSpeed_mps();
    if((cTrajectoryParameters.bGetLengthenPath())&&(dDistance_m < dMinimumPathLength))
    {
        dDistance_m = dMinimumPathLength; 
    }

    double dSegmentTime_sec = (cTrajectoryParameters.dGetSpeed_mps()<=0.0)?(std::numeric_limits<double>::max()):(dDistance_m/cTrajectoryParameters.dGetSpeed_mps());
    cTrajectoryParameters.vGetWaypoints().push_back
                                (CWaypoint(
                                    cTrajectoryParameters.bobjGetStart(),
                                    cTrajectoryParameters.dGetSpeed_mps(),false,
                                    0,
                                    std::numeric_limits<double>::max(),std::numeric_limits<double>::max(),std::numeric_limits<double>::max(),CCircle::turnNone,
                                    cTrajectoryParameters.trjGetParametersEnd().waytypGetFinal(),
                                    cTrajectoryParameters.trjGetParametersEnd().iGetID(),
                                    false,
                                    CWaypoint::sstateFrontCamera,
                                    dSegmentTime_sec
                                ));
    cTrajectoryParameters.vGetWaypoints().back().bGetDoNotRemove() = true;
    cTrajectoryParameters.vGetWaypoints().push_back
                                (CWaypoint(
                                    cTrajectoryParameters.trjGetParametersEnd(),
                                    cTrajectoryParameters.dGetSpeed_mps(),false,
                                    dDistance_m,
                                    std::numeric_limits<double>::max(),std::numeric_limits<double>::max(),std::numeric_limits<double>::max(),CCircle::turnNone,
                                    cTrajectoryParameters.trjGetParametersEnd().waytypGetFinal(),
                                    cTrajectoryParameters.trjGetParametersEnd().iGetID(),
                                    false,
                                    CWaypoint::sstateFrontCamera,
                                    dSegmentTime_sec
                                ));
    cTrajectoryParameters.vGetWaypoints().back().bGetDoNotRemove() = true;

    cTrajectoryParameters.trjGetParametersEndFinal() = cTrajectoryParameters.trjGetParametersEnd();
    cTrajectoryParameters.dGetHeadingFinal_rad() = dHeadingFinal_rad;
    cTrajectoryParameters.dGetDistancePath_m() = dDistance_m;
    return(dDistance_m);
}


double CTrajectory::dMinimumDistanceDubins(CTrajectoryParameters& cTrajectoryParameters,V_TRAJECTORY_PARAMETERS_END_t& vParametersEnd)
{
    // - decide on desired heading to Objective based on Objective and vehicle state.
    // - decide on sensor stand off based on task
    // - decide on free to turn point based on Objective state and desired heading to the Objective.
    // = lengthen path to resolve any conflict with previous task execution time.
    //

    double dDistanceTotalMinimum_m = std::numeric_limits<double>::max();    // defaults to error
    CAssignment assignMinimum;

    CTrajectoryParametersEnd cParametersEndFinal = *vParametersEnd.begin();    //need to keep track of which final parameters were used in the minimum assignment

    // find minimum distance path to all possible endpoint/headings/standoffs
    for(V_TRAJECTORY_PARAMETERS_END_IT_t itParametersEnd=vParametersEnd.begin();itParametersEnd!=vParametersEnd.end();itParametersEnd++)
    {
        for(V_HEADING_PARAMETERS_IT_t itHeadingParameters=itParametersEnd->vGetHeadingParameters().begin();
                                        itHeadingParameters!=itParametersEnd->vGetHeadingParameters().end();
                                        itHeadingParameters++)
        {
            double dHeadingFrom_rad = n_Const::c_Convert::dNormalizeAngleRad((itHeadingParameters->dGetHeadingTo_rad()) + n_Const::c_Convert::dPi(),0.0);
            double dStandoff_m = itHeadingParameters->dGetStandoff_m();

            CAssignment assignTemp;

            switch(cTrajectoryParameters.pathGetType())
            {
            default:
            case CTrajectoryParameters::pathTurnStraightTurn:
            case CTrajectoryParameters::pathDubinMAVWind: //Move the Objectives based on wind calculate the path with dubins
                {
                    // - use desired headings from the Objectives for trajectory generation
                    CPosition posStandoff(dStandoff_m*cos(itHeadingParameters->dGetHeadingTo_rad()),dStandoff_m*sin(itHeadingParameters->dGetHeadingTo_rad()),cTrajectoryParameters.dGetAltitude_m());
                    posStandoff += *itParametersEnd;
                    dCalculateTrajectoryDubins(assignTemp,
                                                cTrajectoryParameters.bobjGetStart(),
                                                cTrajectoryParameters.bobjGetStart().dGetHeading(),
                                                posStandoff,dHeadingFrom_rad,
                                                cTrajectoryParameters.dGetTurnRadius_m(),
                                                cTrajectoryParameters.dGetSpeed_mps(),
                                                cTrajectoryParameters.dGetWaypointSeparationMin_m(),
                                                itParametersEnd->iGetID());
                }
                break;
            case CTrajectoryParameters::pathOptimalMAVWind: //Move the Objectives based on wind calculate the path with dubins adapted to Wind
            case CTrajectoryParameters::pathOptimalMAVWindNoMovedObjectives: //DO NOT Move the Objectives but calculate the path with dubins adapted to Wind
                dMinimumDistanceMAVWind(assignTemp,cTrajectoryParameters,*itParametersEnd,*itHeadingParameters);
                break;
            }
           
            double distanceStartToFirst_m{0.0};;
            if(assignTemp.vwayGetWaypoints().size() > 0)
            {
                distanceStartToFirst_m = cTrajectoryParameters.bobjGetStart().relativeDistance2D_m(assignTemp.vwayGetWaypoints().front());
            }

            
            double dDistanceFinalLeg_m = itHeadingParameters->dGetStandoff_m() - itHeadingParameters->dGetFreeToTurn_m();
            dDistanceFinalLeg_m = (dDistanceFinalLeg_m>0)?(dDistanceFinalLeg_m):(0.0);
            
            double distancePathTotal_m = distanceStartToFirst_m + assignTemp.dGetDistanceTotal() + dDistanceFinalLeg_m;
            
            // check to see if this is the current minimum distance path
            if(n_Const::c_Convert::bCompareDouble(distancePathTotal_m,dDistanceTotalMinimum_m,n_Const::c_Convert::enLess))
            {
                if (assignTemp.vwayGetWaypoints().size()>=1)
                {
                    //set type and objective ID on stand off waypoint. Note: assumes that the last waypoint, at this point, is the stand off waypoint!!!
                    assignTemp.vwayGetWaypoints().back().typeGetWaypoint() = itParametersEnd->waytypGetFinal();
                    assignTemp.vwayGetWaypoints().back().iGetObjectiveID() = itParametersEnd->iGetID();

                    //add free to turn point
                    if((itHeadingParameters->dGetFreeToTurn_m() > 0.0) && (dDistanceFinalLeg_m > 0.0))
                    {
                        CPosition posTemp(itHeadingParameters->dGetFreeToTurn_m()*cos(itHeadingParameters->dGetHeadingTo_rad()),
                                            itHeadingParameters->dGetFreeToTurn_m()*sin(itHeadingParameters->dGetHeadingTo_rad()),
                                            cTrajectoryParameters.dGetAltitude_m());
                        posTemp += *itParametersEnd;
                        assignTemp.iAddWaypoint(CWaypoint(posTemp,
                                                            cTrajectoryParameters.dGetSpeed_mps(),false,
                                                            dDistanceFinalLeg_m,
                                                            std::numeric_limits<double>::max(),std::numeric_limits<double>::max(),std::numeric_limits<double>::max(),CCircle::turnNone,
                                                            CWaypoint::waytypeEnroute,0,false,CWaypoint::sstateFrontCamera));
                    }        //if(tHeadingParameters->dGetFreeToTurn_m() > 0.0)

                    //calculate final segment time
                    if (assignTemp.vwayGetWaypoints().size()>=2)
                    {
                        assignTemp.vwayGetWaypoints()[assignTemp.vwayGetWaypoints().size()-2].erTimeToGo(
                                                            assignTemp.vwayGetWaypoints().back().reGetSegmentTime(),
                                                            assignTemp.vwayGetWaypoints().back(),
                                                            cTrajectoryParameters.dGetWindHeadingFrom_rad()+n_Const::c_Convert::dPi(),
                                                            cTrajectoryParameters.dGetWindSpeed_mps());
                    }

                    assignTemp.vwayGetWaypoints().back().dGetObjectiveDesiredDirection_rad() = itHeadingParameters->dGetHeadingTo_rad();
                    assignTemp.vwayGetWaypoints().back().dGetObjectiveDesiredStandOff_m() = itHeadingParameters->dGetStandoff_m();

                    assignTemp.SetHeadingFinal(dHeadingFrom_rad);
                    assignMinimum = assignTemp;
                    dDistanceTotalMinimum_m = distancePathTotal_m;
                    cParametersEndFinal = *itParametersEnd;
                    cParametersEndFinal.vGetHeadingParameters().clear();
                    cParametersEndFinal.vGetHeadingParameters().push_back(*itHeadingParameters);
                }    //if (assignTemp.vwayGetWaypoints().size()>=2)
            }
        }        //for(V_HEADING_PARAMETERS_IT_t itHeadingParameters=itParametersEnd->vGetHeadingParameters().begin(); ...
    }    //for(V_TRAJECTORY_PARAMETERS_END_IT_t itParametersEnd=vParametersEnd.begin();itParametersEnd!=vParametersEnd.end();itParametersEnd++)

    if(dDistanceTotalMinimum_m != std::numeric_limits<double>::max())
    {
        //return final parameters in cTrajectoryParameters:
        cTrajectoryParameters.trjGetParametersEndFinal() = cParametersEndFinal;
        ////////////////////////////////////////////////////////////////////////////////////////
        // resolve any conflicts in task completion times
        ////////////////////////////////////////////////////////////////////////////////////////
        if(cTrajectoryParameters.bGetLengthenPath())
        {
            //TODO:: this needs to be in terms of time
            double dMinTimeToLengthen_s = cTrajectoryParameters.dGetMinimumTime_s() - 
                                                    (dDistanceTotalMinimum_m*cTrajectoryParameters.dGetSpeed_mps());
            if(dMinTimeToLengthen_s > 0.0)
            {
                dDistanceTotalMinimum_m = dLengthenPath(cTrajectoryParameters,dMinTimeToLengthen_s,assignMinimum);
            }
        }
        cTrajectoryParameters.vGetWaypoints() = assignMinimum.vwayGetWaypoints();
        cTrajectoryParameters.dGetHeadingFinal_rad() = assignMinimum.dGetHeadingFinal();
        cTrajectoryParameters.dGetDistancePath_m() = dDistanceTotalMinimum_m;
    }

    return(dDistanceTotalMinimum_m);
}



///////////////////////////////////////////////////
//CalculateTaskHeading
///////////////////////////////////////////////////
void
CTrajectory::CalculateTaskHeading(CTrajectoryParameters& cTrajectoryParameters)
{

    if(cTrajectoryParameters.trjGetParametersEnd().vGetHeadingParameters().empty())
    {
        double dStandoff_m = cTrajectoryParameters.trjGetParametersEnd().dGetStandOffNoHeadings_m();
        //dStandoff_m = (dStandoff_m < 0.0)?(0.0):(dStandoff_m);
        dStandoff_m = (dStandoff_m < 0.0)?(0.0):(dStandoff_m);

        double dHeadingStart_rad = cTrajectoryParameters.bobjGetStart().dGetHeading();
        V_CIRCLE_t vcircleStart;
        //first center is the clockwise turn (alpha + Pi/2)
        double dCenter1North_m = cTrajectoryParameters.bobjGetStart().m_north_m - cTrajectoryParameters.dGetTurnRadius_m()*sin(dHeadingStart_rad);
        double dCenter1East_m = cTrajectoryParameters.bobjGetStart().m_east_m + cTrajectoryParameters.dGetTurnRadius_m()*cos(dHeadingStart_rad);
        vcircleStart.push_back(CCircle(dCenter1North_m,dCenter1East_m,cTrajectoryParameters.dGetTurnRadius_m(),CCircle::turnClockwise));
        //second center is the counterclockwise turn (alpha - Pi/2)
        dCenter1North_m = cTrajectoryParameters.bobjGetStart().m_north_m + cTrajectoryParameters.dGetTurnRadius_m()*sin(dHeadingStart_rad);
        dCenter1East_m = cTrajectoryParameters.bobjGetStart().m_east_m - cTrajectoryParameters.dGetTurnRadius_m()*cos(dHeadingStart_rad);
        vcircleStart.push_back(CCircle(dCenter1North_m,dCenter1East_m,cTrajectoryParameters.dGetTurnRadius_m(),CCircle::turnCounterclockwise));
        
        
        //ASSERT(vcircleStart.size()==2;);
        double dDesiredHeadingTo = 0.0;
        
        //% Get the necessary distances to be used in the heading calculations
        //%  Get the distance from the vehicle to the Objective
        double dAngleToObjective = 0.0;
        double dDotoF = cTrajectoryParameters.bobjGetStart().relativeDistanceAngle2D_m(cTrajectoryParameters.trjGetParametersEnd(),dAngleToObjective);
        vRound(dDotoF,1.0e-9);
        if(n_Const::c_Convert::bCompareDouble(dDotoF,0.0,n_Const::c_Convert::enEqual))    //vehicle is on top of the Objective, return current vehicle heading
        {
            cTrajectoryParameters.trjGetParametersEnd().vGetHeadingParameters().push_back(CHeadingParameters(dHeadingStart_rad,dStandoff_m));
        }
        else        //if(n_Const::c_Convert::bCompareDouble(dDotoF,0.0,n_Const::c_Convert::enEqual))
        {
            //%  Get the distances from the Objective to the initial turn circle centers
            double dHc1=0.0;
            double dDc1toF = vcircleStart[0].relativeDistanceAngle2D_m(cTrajectoryParameters.trjGetParametersEnd(),dHc1);
            vRound(dDc1toF,1.0e-9);
            
            double dHc2=0.0;
            double dDc2toF = vcircleStart[1].relativeDistanceAngle2D_m(cTrajectoryParameters.trjGetParametersEnd(),dHc2);
            vRound(dDc2toF,1.0e-9);
            
            double dTurnRadius = cTrajectoryParameters.dGetTurnRadius_m();
            
            //% Calculate the minimum distance between the Objective and the final turn circle center to ensure the needed standoff distance
            double dRs = pow((pow(dTurnRadius,2.0) + pow(dStandoff_m,2.0)),0.5);
            vRound(dRs,1.0e-9);
            if(dRs==0.0)
            {
                //TODO::ERROR
                return;
            }
            //% Calculate the headings from the Objective to the initial turn circle centers - used in heading constructions
            dHc1 = n_Const::c_Convert::dPiO2() - dHc1;
            dHc2 = n_Const::c_Convert::dPiO2() - dHc2;
            //% Calculate the angle between the final vehicle position (at sensor standoff distance) and
            //%  the position of final turn circle's center
            double dSliver = atan2(dTurnRadius,dStandoff_m);
            
            //%  Do the geometric constructions of the final vehicle heading depending on the initial position and heading
            //%   of the vehicle with respect to the Objective (final position)
            if ((dDc1toF < dRs) && (dDc2toF < dRs))
            {
                if ((dDc2toF!=0.0)&&((((dDc1toF+2*dTurnRadius) <= dRs) && (dDc1toF < dTurnRadius)) || (dDc1toF <= dDc2toF)))
                {
                    dDesiredHeadingTo = dHc2 - asin(dTurnRadius/dDc2toF) + 2.0*dSliver;
                }
                else if((dDc1toF!=0.0)&&((((dDc2toF + 2.0*dTurnRadius) <= dRs) && (dDc2toF<dTurnRadius)) || (dDc2toF < dDc1toF)))
                {
                    dDesiredHeadingTo = dHc1 + asin(dTurnRadius/dDc1toF) + 2*dSliver;
                }
                else
                {
                    //TODO::error
                }
            }
            else
            {
                double dAngleDifference = n_Const::c_Convert::dNormalizeAngleRad((n_Const::c_Convert::dPiO2() - dHeadingStart_rad) - dAngleToObjective,0.0);
                double dCase = ((dAngleDifference>n_Const::c_Convert::dPiO2())&&(dAngleDifference<n_Const::c_Convert::d3PiO2()))?(1.0):(-1.0);
                if (((dDc2toF >= dRs) && (dDc1toF > dDc2toF)) || ((dDc2toF >= dRs) && (dDc1toF < dRs)))
                {
                    double dFactor = (dTurnRadius/dDc2toF);
                    vRound(dFactor,1.0e-9);
                    double dBeta = -asin(dFactor);
                    
                    dFactor = (-pow(dTurnRadius,2.0) + pow(dDc2toF,2.0) + pow(dDotoF,2.0))/(2*dDc2toF*dDotoF);
                    vRound(dFactor,1.0e-9);
                    double dDelta = acos(dFactor);
                    
                    //double dDelta = acos((-pow(dTurnRadius,2.0) + pow(dDc2toF,2.0) + pow(dDotoF,2.0))/(2*dDc2toF*dDotoF));
                    double dPhi = dBeta + dCase*dDelta;
                    dDesiredHeadingTo = n_Const::c_Convert::dPiO2() - (dAngleToObjective - dPhi);
                }
                else
                {
                    double dFactor = (dTurnRadius/dDc1toF);
                    vRound(dFactor,1.0e-9);
                    double dBeta = asin(dFactor);
                    
                    dFactor = (-pow(dTurnRadius,2.0) + pow(dDc1toF,2.0) + pow(dDotoF,2.0))/(2*dDc1toF*dDotoF);
                    vRound(dFactor,1.0e-9);
                    double dDelta = acos(dFactor);
                    
                    double dPhi = dBeta - dCase*dDelta;
                    dDesiredHeadingTo = n_Const::c_Convert::dPiO2() - (dAngleToObjective - dPhi);
                }
            }
            dDesiredHeadingTo = n_Const::c_Convert::dNormalizeAngleRad(dDesiredHeadingTo,0.0);
            cTrajectoryParameters.trjGetParametersEnd().vGetHeadingParameters().push_back(CHeadingParameters(dDesiredHeadingTo,dStandoff_m));
        }        //if(n_Const::c_Convert::bCompareDouble(dDotoF,0.0,n_Const::c_Convert::enEqual))
    
    }        //if(cTrajectoryParameters.vGetHeadingParameters().empty())
    
}
///////////////////////////////////////////////////
///////////////////////////////////////////////////




double CTrajectory::dLengthenPath(CTrajectoryParameters& cTrajectoryParameters,
                                    double dMinTimeToLengthen_s,CAssignment& assignMinimum)
{
    // ASSUMES::
    // "assignMinimum" contains the following waypoints:
    // The first waypoint is at the end of the first turn/beginning of the straight segment
    // The second waypoint is at the end of the straight segment/beginning of the second turn
    // The third waypoint is at the end of the second turn/beginning of the final segment
    // The forth, and final waypoint, is at the end of the final segment
    // 
    //TODO:: does not respect final heading constraints

    enum enAssignedWaypoints_t {assignwayEndFirstTurn,assignwayEndStraight,assignwayEndSecondTurn,assignwayEndFinal};
    
    CHeadingParameters cHeadingParameters;
    if(!cTrajectoryParameters.trjGetParametersEndFinal().vGetHeadingParameters().empty())
    {
        //ASSUME:: the only heading parameters that count are the first ones in the list, should be the only ones in the list
        cHeadingParameters = cTrajectoryParameters.trjGetParametersEndFinal().vGetHeadingParameters().front();
    }
    double dStandoff_m = cHeadingParameters.dGetStandoff_m();
    double dFreeToTurn_m = cHeadingParameters.dGetFreeToTurn_m();

    //////////////////////////////////////////////////////////////////////////////////
    // ?) calculate radius, center, and direction of loiter path (circle)
    //////////////////////////////////////////////////////////////////////////////////
    double dRadiusTurnCenter_m = sqrt((pow(dStandoff_m,2.0) + pow(cTrajectoryParameters.dGetTurnRadius_m(),2.0)));
    double dRadiusLoiter_m = dRadiusTurnCenter_m + cTrajectoryParameters.dGetTurnRadius_m();
    double dRadiusTurnOnToLoiterMin_m = dRadiusLoiter_m + cTrajectoryParameters.dGetTurnRadius_m();

    //////////////////////////////////////////////////////////////////////////////////
    // ?) calculate final leg distance
    //////////////////////////////////////////////////////////////////////////////////
    double dAngleStandOffRelative_rad = atan(cTrajectoryParameters.dGetTurnRadius_m()/dStandoff_m);
    double dDistanceFinalLeg_m = cTrajectoryParameters.dGetTurnRadius_m()*(n_Const::c_Convert::dPi() - (n_Const::c_Convert::dPiO2() - dAngleStandOffRelative_rad)) + dStandoff_m - dFreeToTurn_m;

    //////////////////////////////////////////////////////////////////////////////////
    // ?) determine case 
    //////////////////////////////////////////////////////////////////////////////////
    CCircle::enTurnDirection_t turndirLoiterDirection = CCircle::turnNone;
    double dAngleLoiterEntryToObjective_rad = std::numeric_limits<double>::max();
    double dDistanceInitialLeg_m = 0.0;
    double dDistanceFirstTangetToObjective = assignMinimum.wayGetWaypoint(assignwayEndFirstTurn).relativeDistance2D_m(cTrajectoryParameters.trjGetParametersEndFinal());
    if(dDistanceFirstTangetToObjective >= dRadiusTurnOnToLoiterMin_m)    //????????????
    {
        //caseOne;
        // case1: outside the required radius. find circle to turn on to loiter circle
        //1. find tangent point to loiter circle
        //2. calculate distance from vehicle to tangent point, first waypoint distance + distance from end of first turn to loiter entry point
        //3. calculate loiter distance required: LoiterDistance = DistanceRequired - (DistanceVehicleToLoiter + DistanceLoiterToFinal)
        //4. remove unused waypoints from the "assignMinimum" waypoints
        //5. calculate new waypoints and pop them onto the "assignMinimum" waypoints
        //6. update final heading, i.e. assignMinimum.SetHeadingFinal(??)

        turndirLoiterDirection = CCircle::turnCounterclockwise;
        
        double dAngleEndFirstTurnToObjective = assignMinimum.wayGetWaypoint(assignwayEndFirstTurn).relativeAngle2D_rad(cTrajectoryParameters.trjGetParametersEndFinal());
        // the following angle calculation assumes a clockwise turn onto the loiter circle
        dAngleLoiterEntryToObjective_rad = dAngleEndFirstTurnToObjective + asin(cTrajectoryParameters.dGetTurnRadius_m()/dRadiusTurnOnToLoiterMin_m);
        double dRadiusLoiterTurnPoint = sqrt(pow(dRadiusTurnOnToLoiterMin_m,2.0) - pow(cTrajectoryParameters.dGetTurnRadius_m(),2.0));

        assignMinimum.EraseWaypoints(assignwayEndStraight);

        CPosition posTemp(dRadiusLoiterTurnPoint*sin(dAngleEndFirstTurnToObjective),
                                    dRadiusLoiterTurnPoint*cos(dAngleEndFirstTurnToObjective),cTrajectoryParameters.dGetAltitude_m());
        posTemp += cTrajectoryParameters.trjGetParametersEndFinal();
        double dDistanceEndFirstTurnToTurnLoiter = assignMinimum.wayGetWaypoint(assignwayEndFirstTurn).relativeDistance2D_m(posTemp);
        assignMinimum.iAddWaypoint(CWaypoint(posTemp,cTrajectoryParameters.dGetSpeed_mps(),false,dDistanceEndFirstTurnToTurnLoiter)
                                                                );
        double dSegmentTime_sec = (cTrajectoryParameters.dGetSpeed_mps()<=0.0)?
                                        (std::numeric_limits<double>::max()):
                                        (dDistanceEndFirstTurnToTurnLoiter/cTrajectoryParameters.dGetSpeed_mps());
        assignMinimum.vwayGetWaypoints().back().reGetSegmentTime() = dSegmentTime_sec;

        double dDistanceTurnToLoiter = cTrajectoryParameters.dGetTurnRadius_m()*acos(cTrajectoryParameters.dGetTurnRadius_m()/dRadiusTurnOnToLoiterMin_m);
        posTemp.m_north_m = dRadiusLoiter_m*sin(dAngleLoiterEntryToObjective_rad);
        posTemp.m_east_m = dRadiusLoiter_m*cos(dAngleLoiterEntryToObjective_rad);
        posTemp.m_altitude_m = cTrajectoryParameters.dGetAltitude_m();
        posTemp += cTrajectoryParameters.trjGetParametersEndFinal();
        assignMinimum.iAddWaypoint(CWaypoint(posTemp,cTrajectoryParameters.dGetSpeed_mps(),false,
                                                                dDistanceTurnToLoiter,
                                                                dRadiusTurnOnToLoiterMin_m*sin(dAngleLoiterEntryToObjective_rad) + cTrajectoryParameters.trjGetParametersEndFinal().m_north_m,
                                                                dRadiusTurnOnToLoiterMin_m*cos(dAngleLoiterEntryToObjective_rad) + cTrajectoryParameters.trjGetParametersEndFinal().m_east_m,
                                                                cTrajectoryParameters.dGetTurnRadius_m(),
                                                                (turndirLoiterDirection==CCircle::turnClockwise)?(CCircle::turnCounterclockwise):(CCircle::turnClockwise))
                                                                );

        dSegmentTime_sec = (cTrajectoryParameters.dGetSpeed_mps()<=0.0)?(std::numeric_limits<double>::max()):(dDistanceTurnToLoiter/cTrajectoryParameters.dGetSpeed_mps());
        assignMinimum.vwayGetWaypoints().back().reGetSegmentTime() = dSegmentTime_sec;

        dDistanceInitialLeg_m = assignMinimum.wayGetWaypoint(assignwayEndFirstTurn).dGetSegmentLength() + 
                                                        dDistanceEndFirstTurnToTurnLoiter + dDistanceTurnToLoiter;
    }
    else
    {
        //caseTwo;
        // case2: path has a tangent to the loiter circle, find it 
        //1. find tangent point to loiter circle
        //2. calculate distance from vehicle to tangent point, first waypoint distance + distance from end of first turn to loiter entry point
        //3. calculate loiter distance required: LoiterDistance = DistanceRequired - (DistanceVehicleToLoiter + DistanceLoiterToFinal)
        //4. remove unused waypoints from the "assignMinimum" waypoints
        //5. calculate new waypoints and pop them onto the "assignMinimum" waypoints
        //6. update final heading, i.e. assignMinimum.SetHeadingFinal(??)

        dAngleLoiterEntryToObjective_rad = assignMinimum.wayGetWaypoint(assignwayEndSecondTurn).circleGetTurn().relativeAngle2D_rad(cTrajectoryParameters.trjGetParametersEndFinal());


        CPosition posTemp(dRadiusLoiter_m*sin(dAngleLoiterEntryToObjective_rad),
                                    dRadiusLoiter_m*cos(dAngleLoiterEntryToObjective_rad),cTrajectoryParameters.dGetAltitude_m());
        posTemp += cTrajectoryParameters.trjGetParametersEndFinal();
        assignMinimum.wayGetWaypoint(assignwayEndSecondTurn) = posTemp;
        double dAngleToLoiter = assignMinimum.wayGetWaypoint(assignwayEndSecondTurn).circleGetTurn().dGetRelativeAngle(
                                                    assignMinimum.wayGetWaypoint(assignwayEndStraight),posTemp);
        dAngleToLoiter = n_Const::c_Convert::dNormalizeAngleRad(dAngleToLoiter,0.0);
        double dDistanceTurnToLoiter = cTrajectoryParameters.dGetTurnRadius_m()*dAngleToLoiter;
        assignMinimum.wayGetWaypoint(assignwayEndSecondTurn).SetSegmentLength(dDistanceTurnToLoiter);
#ifndef BROKEN
        assignMinimum.EraseWaypoints(assignwayEndFinal);
#endif  //broken
        dDistanceInitialLeg_m = assignMinimum.wayGetWaypoint(assignwayEndFirstTurn).dGetSegmentLength() +
                                    assignMinimum.wayGetWaypoint(assignwayEndStraight).dGetSegmentLength() +
                                    dDistanceTurnToLoiter;

        turndirLoiterDirection = assignMinimum.wayGetWaypoint(assignwayEndSecondTurn).circleGetTurn().turnGetTurnDirection();
    }


    double dDistanceLoiter = dMinTimeToLengthen_s - (dDistanceInitialLeg_m + dDistanceFinalLeg_m);
    dDistanceLoiter = (dDistanceLoiter>0.0)?(dDistanceLoiter):(0.0);

    double dAngleLoiter(0.0);
    dAngleLoiter = turndirLoiterDirection*dDistanceLoiter/dRadiusLoiter_m;

#ifdef TODO_CONSTRAIN_FINAL_ANGLE
            //calculate closest final heading for desired time
            double dAngleLoiterSave(dAngleLoiter);
            dAngleLoiter = std::numeric_limits<double>::max(); 
            for(CObjective::V_HEADING_PARAMETERS_IT_t itHeadingParameters=cTrajectoryParameters.trjGetParametersEndFinal().vGetHeadingParameters().begin();itHeadingParameters!=cTrajectoryParameters.trjGetParametersEndFinal().vGetHeadingParameters().end();itHeadingParameters++)
            {
                // - use desired headings from the Objectives for trajectory generation
                double dHeadingFrom_rad = n_Const::c_Convert::dNormalizeAngleRad((itHeadingParameters->dGetHeadingTo_rad()) + n_Const::c_Convert::dPi(),0.0);
                double dAngleTemp = dAngleLoiterEntryToObjective_rad + dAngleLoiterSave + (turndirLoiterDirection*dHeadingFrom_rad);
                if(dAngleTemp < dAngleLoiter)
                {
                    dAngleLoiter = dAngleTemp;
                }
            }
#endif        //TODO_CONSTRAIN_FINAL_ANGLE

    double dAngleLoiterIncrement = turndirLoiterDirection*dGetAngleLoiterIncrement_rad();
    
    // add a waypoint evey "dGetAngleLoiterIncrement_rad()" radians along the loiter circle
    double dDistanceLoiterSegment = dGetAngleLoiterIncrement_rad()*dRadiusLoiter_m;
    double dAngleLoiterTemp = dAngleLoiterIncrement;
    double dAnglePointIncrement_rad = 0.0;
    while((turndirLoiterDirection!=CCircle::turnNone)&&(fabs(dAngleLoiterTemp) <= fabs(dAngleLoiter)))
    {
        dAnglePointIncrement_rad = dAngleLoiterTemp + dAngleLoiterEntryToObjective_rad;
        CPosition posTemp(dRadiusLoiter_m*sin(dAnglePointIncrement_rad),
                                    dRadiusLoiter_m*cos(dAnglePointIncrement_rad),
                                    cTrajectoryParameters.dGetAltitude_m());
        posTemp += cTrajectoryParameters.trjGetParametersEndFinal();
        assignMinimum.iAddWaypoint(CWaypoint(posTemp,cTrajectoryParameters.dGetSpeed_mps(),false,
                                                                dDistanceLoiterSegment,
                                                                cTrajectoryParameters.trjGetParametersEndFinal().m_north_m,cTrajectoryParameters.trjGetParametersEndFinal().m_east_m,dRadiusLoiter_m,turndirLoiterDirection)
                                                                );
        double dSegmentTime_sec = (cTrajectoryParameters.dGetSpeed_mps()<=0.0)?(std::numeric_limits<double>::max()):(dDistanceLoiterSegment/cTrajectoryParameters.dGetSpeed_mps());
        assignMinimum.vwayGetWaypoints().back().reGetSegmentTime() = dSegmentTime_sec;
        dAngleLoiterTemp += dAngleLoiterIncrement;
    }
    // add last waypoint on the loiter trajectory
    double dAnglePointLoiterFinal_rad = dAngleLoiter + dAngleLoiterEntryToObjective_rad;

    CPosition posTemp(dRadiusLoiter_m*sin(dAnglePointLoiterFinal_rad),
                                dRadiusLoiter_m*cos(dAnglePointLoiterFinal_rad),
                                cTrajectoryParameters.dGetAltitude_m());
    posTemp += cTrajectoryParameters.trjGetParametersEndFinal();
    double dDistanceToFinalLeg = dRadiusLoiter_m*fabs(dAngleLoiter-(dAngleLoiterTemp - dAngleLoiterIncrement));
    assignMinimum.iAddWaypoint(CWaypoint(posTemp,cTrajectoryParameters.dGetSpeed_mps(),false,
                                                            dDistanceToFinalLeg,
                                                            cTrajectoryParameters.trjGetParametersEndFinal().m_north_m,cTrajectoryParameters.trjGetParametersEndFinal().m_east_m,dRadiusLoiter_m,turndirLoiterDirection)
                                                            );
    double dSegmentTime_sec = (cTrajectoryParameters.dGetSpeed_mps()<=0.0)?(std::numeric_limits<double>::max()):(dDistanceToFinalLeg/cTrajectoryParameters.dGetSpeed_mps());
    assignMinimum.vwayGetWaypoints().back().reGetSegmentTime() = dSegmentTime_sec;

    double dAngleStandOff_rad = dAnglePointLoiterFinal_rad + (turndirLoiterDirection*dAngleStandOffRelative_rad);

    posTemp.m_north_m = dStandoff_m*sin(dAngleStandOff_rad);
    posTemp.m_east_m = dStandoff_m*cos(dAngleStandOff_rad);
    posTemp.m_altitude_m = cTrajectoryParameters.dGetAltitude_m();
    posTemp += cTrajectoryParameters.trjGetParametersEndFinal();
    double dDistanceFinalLeg = cTrajectoryParameters.dGetTurnRadius_m()*(n_Const::c_Convert::dPi() - (n_Const::c_Convert::dPiO2() - dAngleStandOffRelative_rad));
    assignMinimum.iAddWaypoint(CWaypoint(posTemp,cTrajectoryParameters.dGetSpeed_mps(),false,
                                                            dDistanceFinalLeg,
                                                            (dRadiusLoiter_m - cTrajectoryParameters.dGetTurnRadius_m())*sin(dAnglePointLoiterFinal_rad) + cTrajectoryParameters.trjGetParametersEndFinal().m_north_m,
                                                            (dRadiusLoiter_m - cTrajectoryParameters.dGetTurnRadius_m())*cos(dAnglePointLoiterFinal_rad) + cTrajectoryParameters.trjGetParametersEndFinal().m_east_m,
                                                            cTrajectoryParameters.dGetTurnRadius_m(),turndirLoiterDirection)
                                                            );

    dSegmentTime_sec = (cTrajectoryParameters.dGetSpeed_mps()<=0.0)?(std::numeric_limits<double>::max()):(dDistanceFinalLeg/cTrajectoryParameters.dGetSpeed_mps());
    assignMinimum.vwayGetWaypoints().back().reGetSegmentTime() = dSegmentTime_sec;

    posTemp.m_north_m = dFreeToTurn_m*sin(dAngleStandOff_rad);
    posTemp.m_east_m = dFreeToTurn_m*cos(dAngleStandOff_rad);
    posTemp.m_altitude_m = cTrajectoryParameters.dGetAltitude_m();
    posTemp += cTrajectoryParameters.trjGetParametersEndFinal();

    double dDistanceFinalFinalLeg = dStandoff_m - dFreeToTurn_m;
    assignMinimum.iAddWaypoint(CWaypoint(posTemp,cTrajectoryParameters.dGetSpeed_mps(),false,
                                        dDistanceFinalFinalLeg,std::numeric_limits<double>::max(),std::numeric_limits<double>::max(),std::numeric_limits<double>::max(),CCircle::turnNone,
                                        cTrajectoryParameters.trjGetParametersEndFinal().waytypGetFinal(),cTrajectoryParameters.trjGetParametersEndFinal().iGetID(),false)
                                        );
    //TODO:: check Objective heading and standoff
    dSegmentTime_sec = (cTrajectoryParameters.dGetSpeed_mps()<=0.0)?(std::numeric_limits<double>::max()):(dDistanceFinalFinalLeg/cTrajectoryParameters.dGetSpeed_mps());
    assignMinimum.vwayGetWaypoints().back().reGetSegmentTime() = dSegmentTime_sec;

    assignMinimum.SetHeadingFinal(n_Const::c_Convert::dPiO2() - dAngleStandOff_rad + n_Const::c_Convert::dPi());
//    assignMinimum.SetHeadingFinal(n_Const::c_Convert::dPiO2() - dAngleStandOff_rad);

    return(dDistanceInitialLeg_m + dDistanceLoiter + dDistanceFinalLeg_m);
}        //double CTrajectory::dLengthenPath



////////////////////////////////////////////////////////////////////
//MAVWind functionalities added by Nicola Ceccarelli (Sept. 2006)///
////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////


double CTrajectory::dMinimumDistanceMAVWind(CAssignment& assignMinimum,
                                            CTrajectoryParameters& cTrajectoryParameters,
                                            CTrajectoryParametersEnd& trjParametersEnd,
                                            CHeadingParameters& rHeadingParameters)
{
    
    
    //Returning variable
    double RetFLAG=-1.0;
    
    //variables for the path planner
    // TODO:: 10 is an arbitrary number
    int iMaxNumberSegmentsInTurn = (cTrajectoryParameters.dGetWaypointSeparationMin_m()<=0.0)?(10):
                                        static_cast<int>(2.0*n_Const::c_Convert::dPi()*cTrajectoryParameters.dGetTurnRadius_m()/cTrajectoryParameters.dGetWaypointSeparationMin_m());
    iMaxNumberSegmentsInTurn = (iMaxNumberSegmentsInTurn < 1)?(1):(iMaxNumberSegmentsInTurn);

    // maximum angular change allowed in nowind
    double alpha = 2.0*n_Const::c_Convert::dPi()/static_cast<double>(iMaxNumberSegmentsInTurn); 
    
    
    // minimum length step set based on turn radius and minimum number of points on circle
    double minStep_m = cTrajectoryParameters.dGetTurnRadius_m()*sin(alpha/2.0); 
    
    
    double dSensorStandoff_m = rHeadingParameters.dGetStandoff_m();

    double Vwind_mps[2];//wind velocity to be moved outside this function
    //TODO:: need to check this for from/to directions
        Vwind_mps[0]=cTrajectoryParameters.dGetWindSpeed_mps()*cos(cTrajectoryParameters.dGetWindHeadingFrom_rad());
        Vwind_mps[1]=cTrajectoryParameters.dGetWindSpeed_mps()*sin(cTrajectoryParameters.dGetWindHeadingFrom_rad());

    
    /*transformation of initial and final heading to the no wind moving Objective scenarios 
    by adding waypoints I will remove the last at the end, see "Figure" in the paper*/
    
    double firstStep_m = 10.0;
    

    //first couple of waypoints is artificial will be removed at the end
    double WayPointFirstIN[2]; 
        WayPointFirstIN[0] = cTrajectoryParameters.bobjGetStart().m_north_m - firstStep_m*cos(cTrajectoryParameters.bobjGetStart().dGetHeading());
        WayPointFirstIN[1] = cTrajectoryParameters.bobjGetStart().m_east_m - firstStep_m*sin(cTrajectoryParameters.bobjGetStart().dGetHeading());

    //the second waypoint is based on the stand off distance
    double WayPointSecondIN[2]; 
        WayPointSecondIN[0]=cTrajectoryParameters.bobjGetStart().m_north_m;
        WayPointSecondIN[1]=cTrajectoryParameters.bobjGetStart().m_east_m;
    
    //last couple of waypoints
        double WayPointSecondOUT[2];//will be removed and added out of this function
        double WayPointFirstOUT[2];
        if (dSensorStandoff_m>0.0)
        {
            
            WayPointSecondOUT[0] = trjParametersEnd.m_north_m;
            WayPointSecondOUT[1] = trjParametersEnd.m_east_m;
        
                
            WayPointFirstOUT[0] =  trjParametersEnd.m_north_m + dSensorStandoff_m*cos(rHeadingParameters.dGetHeadingTo_rad());
            WayPointFirstOUT[1] =  trjParametersEnd.m_east_m + dSensorStandoff_m*sin(rHeadingParameters.dGetHeadingTo_rad());
        }
        else
        {
            WayPointSecondOUT[0] =  trjParametersEnd.m_north_m - 10.0*cos(rHeadingParameters.dGetHeadingTo_rad());;
            WayPointSecondOUT[1] =  trjParametersEnd.m_east_m - 10.0*sin(rHeadingParameters.dGetHeadingTo_rad());
            
            WayPointFirstOUT[0] =  trjParametersEnd.m_north_m;
            WayPointFirstOUT[1] =  trjParametersEnd.m_east_m;
        }
    
    //move the second waypoint to the no wind scenario
    double Step[2];
    Step[0]=WayPointSecondIN[0]-WayPointFirstIN[0];
    Step[1]=WayPointSecondIN[1]-WayPointFirstIN[1];

    //MATLAB: a=vWpIn^2-Vw(1)^2-Vw(2)^2;
    double a=pow(cTrajectoryParameters.dGetSpeed_mps(),2)-pow(Vwind_mps[0],2)-pow(Vwind_mps[1],2);
    //MATLAB: b=2*(StepIn(1)*Vw(1)+StepIn(2)*Vw(2));
    double b=2*(Step[0]*Vwind_mps[0]+Step[1]*Vwind_mps[1]);
    //MATLAB:c=-StepIn(1)^2-StepIn(2)^2;
    double c=-pow(Step[0],2)-pow(Step[1],2);
    //MATLAB:TStepIn=(-b+sqrt(b^2-4*a*c))/(2*a);
    double TStepIN=(-b+sqrt(pow(b,2)-4*a*c))/(2*a);
    
    //move the second waypoint to the new location, it will be moved back later
    WayPointSecondIN[0]=WayPointSecondIN[0]-TStepIN*Vwind_mps[0];
    WayPointSecondIN[1]=WayPointSecondIN[1]-TStepIN*Vwind_mps[1];
    
    //move the last waypoint to the no wind scenario without traslation
    Step[0] = WayPointSecondOUT[0]-WayPointFirstOUT[0];
    
    Step[1] = WayPointSecondOUT[1]-WayPointFirstOUT[1];
    //MATLAB: b=2*(StepOut(1)*Vw(1)+StepOut(2)*Vw(2));
    b=2*(Step[0]*Vwind_mps[0]+Step[1]*Vwind_mps[1]);
    //MATLAB:c=-StepOut(1)^2-StepOut(2)^2;
    c=-pow(Step[0],2)-pow(Step[1],2);
    //MATLAB:TStepIn=(-b+sqrt(b^2-4*a*c))/(2*a);
    double TStepOUT=(-b+sqrt(pow(b,2)-4*a*c))/(2*a);
    
    //move the last waypoint to the new location, it will be moved back later
    WayPointSecondOUT[0]=WayPointSecondOUT[0]-TStepOUT*Vwind_mps[0];
    WayPointSecondOUT[1]=WayPointSecondOUT[1]-TStepOUT*Vwind_mps[1];
    
    /*generate a North-West and North-East limit turns composed by segments of length minStep_m 
    and angular difference alpha for the initial and final couple of waypoints*/
    
    std::vector<std::vector<double>> ZinNE=FindLimitTurn(WayPointFirstIN,WayPointSecondIN,alpha,minStep_m);
    std::vector<std::vector<double>> ZinNW=FindLimitTurn(WayPointFirstIN,WayPointSecondIN,-alpha,minStep_m);
    std::vector<std::vector<double>> ZOutNE=FindLimitTurn(WayPointSecondOUT,WayPointFirstOUT,alpha,minStep_m);
    std::vector<std::vector<double>> ZOutNW=FindLimitTurn(WayPointSecondOUT,WayPointFirstOUT,-alpha,minStep_m);
    
    
    //length first segment
    double lengthFirstSgment_m=TStepIN*cTrajectoryParameters.dGetSpeed_mps();
    bool foundPath[4]={false,false,false,false};
    double timePaths[4]={0,0,0,0};
    
    //find the minmum time path RSR
    std::vector<std::vector<double>> ZRSR=FindPathBetweenTurns(ZinNE,ZOutNW,lengthFirstSgment_m,minStep_m,alpha,cTrajectoryParameters.dGetSpeed_mps(),Vwind_mps,timePaths[0],foundPath[0]);
    //find the minmum time path RSL
    std::vector<std::vector<double>> ZRSL=FindPathBetweenTurns(ZinNE,ZOutNE,lengthFirstSgment_m,minStep_m,alpha,cTrajectoryParameters.dGetSpeed_mps(),Vwind_mps,timePaths[1],foundPath[1]);
    //find the minmum time path LSR
    std::vector<std::vector<double>> ZLSR=FindPathBetweenTurns(ZinNW,ZOutNW,lengthFirstSgment_m,minStep_m,alpha,cTrajectoryParameters.dGetSpeed_mps(),Vwind_mps,timePaths[2],foundPath[2]);
    //find the minmum time path LSL
    std::vector<std::vector<double>> ZLSL=FindPathBetweenTurns(ZinNW,ZOutNE,lengthFirstSgment_m,minStep_m,alpha,cTrajectoryParameters.dGetSpeed_mps(),Vwind_mps,timePaths[3],foundPath[3]);
    
    //searching the minimum time path
    int Kstar=-1;
    double Tstar=-1;
    for (int k=0;k<=3;k++){
        if (foundPath[k] & (Kstar<0)){
            Kstar=k+1;
            Tstar=timePaths[k];
        }
        else if (foundPath[k] & (timePaths[k]<Tstar)){
            Kstar=k+1;
            Tstar=timePaths[k];
        }
    }
    
    std::vector<std::vector<double>> Ztmp;
    std::vector<double> Zelemtemp;
    
    std::vector<std::vector<double>> Zstar; //here the optimal path
    
    if (Kstar>0){
        switch (Kstar){
        case 1:
            Ztmp=ZRSR;
            break;
        case 2:
            Ztmp=ZRSL;
            break;
        case 3:
            Ztmp=ZLSR;
            break;
        case 4:
            Ztmp=ZLSL;
            break;
        }
        
        /* Now we go back to the wind static Objective scenario*/
        
        //remove the last waypoint it is fake
        Ztmp.pop_back();
        double U[2];
        double TU_sec;
        Zstar.push_back(Ztmp[0]);
        size_t k;
        for (k=1;k<=Ztmp.size()-1;k++){
            //MATLAB CODE:U=Z(:,2:end)-Z(:,1:end-1);
            //step
            U[0]=Ztmp[k][0]-Ztmp[k-1][0];
            U[1]=Ztmp[k][1]-Ztmp[k-1][1];
            
            //MATLAB CODE:T(i)=norm(U(:,i))/v;
            //Time step
            TU_sec=sqrt(pow(U[0],2)+pow(U[1],2))/cTrajectoryParameters.dGetSpeed_mps();
            
            
            //MATLAB CODE: Zout=[Zout Zout(:,end)+U(:,i)+Vw*T(i)];
            Zelemtemp=Zstar[k-1];
            Zelemtemp[0]=Zelemtemp[0]+U[0]+Vwind_mps[0]*TU_sec;
            Zelemtemp[1]=Zelemtemp[1]+U[1]+Vwind_mps[1]*TU_sec;
            
            Zstar.push_back(Zelemtemp);        
        }//(int k=0;k<=Ztmp.size()-1;k++)

        //Setting waypoint vehicle

        for (k=2;k<=Zstar.size()-1;k++)
        {
            //remove the first waypoint is FAKE
            CWaypoint waypoint(Zstar[k][0],Zstar[k][1],cTrajectoryParameters.dGetAltitude_m(),cTrajectoryParameters.dGetSpeed_mps(),false);
            if (k>2)
            {
                assignMinimum.vwayGetWaypoints().back().erTimeToGo(waypoint.reGetSegmentTime(),waypoint,
                                                                    cTrajectoryParameters.dGetWindHeadingFrom_rad()+n_Const::c_Convert::dPi(),cTrajectoryParameters.dGetWindSpeed_mps());
                waypoint.dGetSegmentLength() = assignMinimum.vwayGetWaypoints().back().relativeDistance2D_m(waypoint);
            }
            assignMinimum.iAddWaypoint(waypoint);
#ifdef TODO    //need to add distances to these waypoints
            double dSegmentTime_sec = (cTrajectoryParameters.dGetSpeed_mps()<=0.0)?(std::numeric_limits<double>::max()):(dDistanceToFinalLeg/cTrajectoryParameters.dGetSpeed_mps());
            assignMinimum.vwayGetWaypoints().back().reGetSegmentTime() = dSegmentTime_sec;
#endif    //TODO
        }
//RAS:: I'm assuming that the last waypoint is the Objective action point and the one before that is the stand-off point
        if((assignMinimum.vwayGetWaypoints().end()-1) != assignMinimum.vwayGetWaypoints().begin())
        {
            (assignMinimum.vwayGetWaypoints().end()-1)->iGetObjectiveID() =  trjParametersEnd.iGetID();
        }
        
        // FAKE DISTANCE !!!!!!!! IS TIME*AIRSPEED
        RetFLAG=Tstar*cTrajectoryParameters.dGetSpeed_mps(); 
        
        
    }//if (Kstar>0)
    else
    {
        RetFLAG=-1;
    }
    
    
    return(RetFLAG);
    
}

std::vector<std::vector<double>> CTrajectory::FindLimitTurn(double* Waypoint1,double* Waypoint2,double alpha,double minStep)
{
    
    // number of turns to accomplish a complete turn
    int N=static_cast<int>(ceil(n_Const::c_Convert::dTwoPi()/fabs(alpha)));
    
    //inizialization vector
    std::vector<double> W;
    W.resize(2,0.0);
    std::vector<std::vector<double>> Z;
    //Z.resize(N);
    //insert first waypoint
    W[0]=Waypoint1[0];
    W[1]=Waypoint1[1];
    Z.push_back(W);
    //insert second waypoint
    W[0]=Waypoint2[0];
    W[1]=Waypoint2[1];
    Z.push_back(W);

    for(int k=1;k<=N-1;k++){
        //MATLAB: thetaSup=atan2(ZinSup(2,end)-ZinSup(2,end-1),ZinSup(1,end)-ZinSup(1,end-1));
        double theta1= n_Const::c_Convert::dNormalizeAngleRad(n_Const::c_Convert::dPiO2()-atan2(Z[k][0]-Z[k-1][0],Z[k][1]-Z[k-1][1]));
        //MATLAB: Asup=angModPi(AthetaSup+alpha);
        double theta2= n_Const::c_Convert::dNormalizeAngleRad(theta1+alpha);
        //MATLAB: ZinSup=[ZinSup ZinSup(:,end)+minStep*[cos(Asup);sin(Asup)]];
        W[0]=Z.back()[0]+minStep*cos(theta2);
        W[1]=Z.back()[1]+minStep*sin(theta2);
        Z.push_back(W);
    }return(Z);
}

//This function find a path between two limit turns and the time to accomplish it
std::vector<std::vector<double>> CTrajectory::FindPathBetweenTurns(std::vector<std::vector<double>> Turn1,std::vector<std::vector<double>> Turn2,double LengthFirstSegment,double RegularStep,double MaxDirChange, double AirSpeed, double* Vwind, double& TimePath,bool& Found){
    std::vector<std::vector<double>> Z;
    std::vector<double> Zelem;
    bool found=false; //flag if the path has been found
    bool cond1,cond2;
    int N=Turn1.size();
    double Step[2]; //connection step
    double rhoc,rho1,rho2;
    double T,Dir;
    double a,b,c;
    
    for (int k=1;k<=N-1;k++){
        std::vector<double> A=Turn1[k];
        std::vector<double> Aroot=Turn1[k-1];
        
        for (int j=1;j<=N-1;j++){
            std::vector<double> B=Turn2[j];
            std::vector<double> Broot=Turn2[j-1];            
            Step[0]=B[0]-A[0];
            Step[1]=B[1]-A[1];
            rho1=(k-1)*RegularStep;
            rho2=(j-1)*RegularStep;
            
            //rhoc=rho1+rho2+TStepIn*vWpIn;
            /* MATLAB code:
            rhoc=rho1+rho2+TStepIn*vWpIn;
            a=v^2-Vw(1)^2-Vw(2)^2;
            b=2*(Step(1)*Vw(1)+Step(2)*Vw(2)-rhoc*v);
            c=rhoc^2-Step(1)^2-Step(2)^2;
            Tstar=(-b+sqrt(b^2-4*a*c))/(2*a);*/
            rhoc=rho1+rho2+LengthFirstSegment;
            a=pow(AirSpeed,2)-pow(Vwind[0],2)-pow(Vwind[1],2);
            b=2*(Step[0]*Vwind[0]+Step[1]*Vwind[1]-rhoc*AirSpeed);
            c=pow(rhoc,2)-pow(Step[0],2)-pow(Step[1],2);
            T=(-b+sqrt(pow(b,2)-4*a*c))/(2*a);
            if ((!Found) | ((Found) & (T<TimePath))){
                /* MATLAB CODE: move the B point in agree with the time T required to accomplish the path, I'm substantially moving all the limit turn 
                        B=B-[Vw(1)*Tstar; Vw(2)*Tstar];
                        Broot=Broot-[Vw(1)*Tstar; Vw(2)*Tstar];*/

                B[0]=B[0]-Vwind[0]*T;
                B[1]=B[1]-Vwind[1]*T;
                Broot[0]=Broot[0]-Vwind[0]*T;
                Broot[1]=Broot[1]-Vwind[1]*T;
                
                //direction of the Step in the nowind moving Objective scenario
                // MATLAB CODE: Dir=atan2(Step(2)-Vw(2)*Tstar,Step(1)-Vw(1)*Tstar);
                Dir= n_Const::c_Convert::dNormalizeAngleRad(n_Const::c_Convert::dPiO2()-atan2(Step[0]-Vwind[0]*T,Step[1]-Vwind[1]*T));    
                
                //MATLAB CODE:found=(chekFeasible(Asup,Ainf,Dir)) & (chekFeasible(Bsup,Binf,Dir)) & (norm(Step)>minStep) & (Tstar<=Tbest);
                
                cond1=isStepFeasible(Dir,A,Aroot,B,Broot, MaxDirChange); 
                cond2=(sqrt(pow(Step[0],2)+pow(Step[1],2))>=RegularStep);
                found= cond1 & cond2;
            
                
                //generate the path

                if (found){

                    Z.clear();
                    TimePath=T;
                    Found= true;
                for (int tk=0;tk<=k;tk++) {
                        Z.push_back(Turn1[tk]);
                    }
                    for (int tj=j;tj>=0;tj--){

                        //move the second turn opposite to the wind direction for time T
                        Zelem=Turn2[tj];
                        Zelem[0]=Zelem[0]-Vwind[0]*T;
                        Zelem[1]=Zelem[1]-Vwind[1]*T;
                        Z.push_back(Zelem);
                    }

                }//if (found)

            }//if (!found | (found & T<TimePath)
        }//for (int j=2;j<=N;j++)

    }//(int k=1;k<=N-1;k++)

return(Z);
}

//This function check if the connection step between two turns is feasible w.r.t. the angular constraints alpha in the no wind moving Objective scenario 
bool CTrajectory::isStepFeasible(double Dir,std::vector<double> A,std::vector<double> Aroot,std::vector<double> B,std::vector<double> Broot,double alpha){

    bool outA=false;
    bool outB=false;
    /*MATLAB CODE
    Atheta=atan2(A(2)-Aroot(2),A(1)-Aroot(1));
    Btheta=atan2(-(B(2)-Broot(2)),-(B(1)-Broot(1)));

    Asup=angModPi(Atheta+alpha);
    Ainf=angModPi(Atheta-alpha);

    Bsup=angModPi(Btheta+alpha);
    Binf=angModPi(Btheta-alpha);*/
    double Atheta= n_Const::c_Convert::dNormalizeAngleRad(n_Const::c_Convert::dPiO2()-atan2(A[0]-Aroot[0],A[1]-Aroot[1]));
    double Btheta= n_Const::c_Convert::dNormalizeAngleRad(n_Const::c_Convert::dPiO2()-atan2(-(B[0]-Broot[0]),-(B[1]-Broot[1])));
    
    double Asup= n_Const::c_Convert::dNormalizeAngleRad(Atheta+alpha);
    double Ainf= n_Const::c_Convert::dNormalizeAngleRad(Atheta-alpha);

    double Bsup= n_Const::c_Convert::dNormalizeAngleRad(Btheta+alpha);
    double Binf= n_Const::c_Convert::dNormalizeAngleRad(Btheta-alpha);

    /*MATLAB CODE
    function a=chekFeasible(Sup,Inf,Dir)
    
      if abs(Sup)>pi|abs(Dir)>pi|abs(Inf)>pi
      error('angle out of pi bound!');
      end
      if sign(Sup)<sign(Inf)
      if sign(Dir)<=0
      a=Dir<Sup;
      elseif sign(Dir)>0
      a=Dir>Inf;
      end
      else
      a=(Dir<Sup)&(Dir>Inf);
      end
      */
    if ( ((Asup)/fabs(Asup)) < ((Ainf)/fabs(Ainf)) ){
        if (Dir<0)  outA=(Dir<=Asup);
        else if (Dir>0)  outA=(Dir>=Ainf);
    }//if (Asup)/abs(Asup)<(Ainf)/abs(Ainf)
    else  outA=(Dir<Asup) & (Dir>=Ainf);
    
    if ( ((Bsup)/fabs(Bsup)) < ((Binf)/fabs(Binf)) ){
        if (Dir<0)  outB=(Dir<Bsup);
        else if (Dir>0)  outB=(Dir>Binf);
    }//if (Asup)/abs(Asup)<(Ainf)/abs(Ainf)
    else  outB=(Dir<Bsup) & (Dir>Binf);
    return(outA & outB);
}

//This function moves the endpoint in order to compensate for wind (used for sensors with fixed azimuth angle )
//ASSUMPTION:: command airspeed is commanded, not groundspeed ????
//TODO:: I'm not sure that this function will work correctley
void CTrajectory::CompensateEndPointsForWind(CTrajectoryParameters& cTrajectoryParameters,V_TRAJECTORY_PARAMETERS_END_t& vParametersEnd)
{
    vParametersEnd.clear();    //just in case

    // calculate components of the windspeed towards the north and east directions
    double dWindSpeedNorth_mps = cTrajectoryParameters.dGetWindSpeed_mps()*cos(cTrajectoryParameters.dGetWindHeadingFrom_rad() + n_Const::c_Convert::dPi());
    double dWindSpeedEast_mps = cTrajectoryParameters.dGetWindSpeed_mps()*sin(cTrajectoryParameters.dGetWindHeadingFrom_rad() + n_Const::c_Convert::dPi());

    CTrajectoryParametersEnd& rtrjParameterEnd = cTrajectoryParameters.trjGetParametersEnd();
    for (V_HEADING_PARAMETERS_IT_t itHeadingParameters=rtrjParameterEnd.vGetHeadingParameters().begin();
                                    itHeadingParameters!=rtrjParameterEnd.vGetHeadingParameters().end();
                                    itHeadingParameters++)
    {
        double dDesiredHeadingTo_rad = itHeadingParameters->dGetHeadingTo_rad() + cTrajectoryParameters.dGetSensorAzimuth_rad();
        //TODO:: need to check to make sure this is the correct desired angle

        double dAirspeedNorth_mps = cTrajectoryParameters.dGetSpeed_mps()*cos(dDesiredHeadingTo_rad + n_Const::c_Convert::dPi());
        double dAirspeedEast_mps = cTrajectoryParameters.dGetSpeed_mps()*sin(dDesiredHeadingTo_rad + n_Const::c_Convert::dPi());
        double dGroundspeedNorth_mps = dAirspeedNorth_mps + dWindSpeedNorth_mps;
        double dGroundspeedEast_mps = dAirspeedEast_mps + dWindSpeedEast_mps;
        double dNewHeadingTo_rad = atan2(dGroundspeedEast_mps,dGroundspeedNorth_mps) + n_Const::c_Convert::dPi();

        CTrajectoryParametersEnd trjParametersEnd(rtrjParameterEnd);
        trjParametersEnd.m_north_m += cos(dDesiredHeadingTo_rad)*cTrajectoryParameters.dGetSensorCenter_m();
        trjParametersEnd.m_east_m += sin(dDesiredHeadingTo_rad)*cTrajectoryParameters.dGetSensorCenter_m();
        
        trjParametersEnd.vGetHeadingParameters().clear();
        trjParametersEnd.vGetHeadingParameters().push_back(
                    CHeadingParameters(dNewHeadingTo_rad,itHeadingParameters->dGetStandoff_m(),itHeadingParameters->dGetFreeToTurn_m()));

        vParametersEnd.push_back(trjParametersEnd);
    }
}



double CTrajectory::dCalculateTrajectoryDubins(CAssignment& assignMinimum,
                                                      const CPosition& pointInitial,const double& dHeadingInitial_rad,
                                                      const CPosition& pointFinal,double& dHeadingFinal_rad,
                                                      const double& dTurnRadius_m,
                                                      const double& dCommandSpeed_mps,
                                                      const double& dMinimumWaypointSeparation_m,
                                                      const double& dObjectID)
{

    //  This function calculates the minimum path between two points
    //  given the position of the points and the required headings.
    //  Assuming constant turn radius, and constant altitude

    ////////////////////////////////////////////////////////////////////////////////////////
    // find minimum distance path
    ////////////////////////////////////////////////////////////////////////////////////////
    V_CIRCLE_t vcircleInitial;
    //first center is the clockwise turn (alpha + Pi/2)
    double dCenterNorth_m = pointInitial.m_north_m + dTurnRadius_m*cos(dHeadingInitial_rad + n_Const::c_Convert::dPiO2());
    double dCenterEast_m = pointInitial.m_east_m + dTurnRadius_m*sin(dHeadingInitial_rad + n_Const::c_Convert::dPiO2());
    vcircleInitial.push_back(CCircle(dCenterNorth_m,dCenterEast_m,dTurnRadius_m,CCircle::turnClockwise));
    //second center is the counterclockwise turn (alpha - Pi/2)
    dCenterNorth_m = pointInitial.m_north_m + dTurnRadius_m*cos(dHeadingInitial_rad - n_Const::c_Convert::dPiO2());
    dCenterEast_m = pointInitial.m_east_m + dTurnRadius_m*sin(dHeadingInitial_rad - n_Const::c_Convert::dPiO2());
    vcircleInitial.push_back(CCircle(dCenterNorth_m,dCenterEast_m,dTurnRadius_m,CCircle::turnCounterclockwise));


    V_CIRCLE_t vcircleFinal;
    //first center is the clockwise turn (alpha + Pi/2)
    dCenterNorth_m = pointFinal.m_north_m + dTurnRadius_m*cos(dHeadingFinal_rad + n_Const::c_Convert::dPiO2());
    dCenterEast_m = pointFinal.m_east_m + dTurnRadius_m*sin(dHeadingFinal_rad + n_Const::c_Convert::dPiO2());
    vcircleFinal.push_back(CCircle(dCenterNorth_m,dCenterEast_m,dTurnRadius_m,CCircle::turnClockwise));
    //second center is the counterclockwise turn (alpha - Pi/2)
    dCenterNorth_m = pointFinal.m_north_m + dTurnRadius_m*cos(dHeadingFinal_rad - n_Const::c_Convert::dPiO2());
    dCenterEast_m = pointFinal.m_east_m + dTurnRadius_m*sin(dHeadingFinal_rad - n_Const::c_Convert::dPiO2());
    vcircleFinal.push_back(CCircle(dCenterNorth_m,dCenterEast_m,dTurnRadius_m,CCircle::turnCounterclockwise));
    
        
    double dDistanceTotalMinimum_m = std::numeric_limits<double>::max();    // need to find shortest distance

    for(V_CIRCLE_IT_t itTurnInitial=vcircleInitial.begin();itTurnInitial!=vcircleInitial.end();itTurnInitial++)
    {
        for(V_CIRCLE_IT_t itTurnFinal=vcircleFinal.begin();itTurnFinal!=vcircleFinal.end();itTurnFinal++)
        {
            if((itTurnInitial->turnGetTurnDirection() == itTurnFinal->turnGetTurnDirection())||
                n_Const::c_Convert::bCompareDouble(itTurnInitial->relativeDistance2D_m(*itTurnFinal),
                                    itTurnInitial->dGetRadius() + itTurnFinal->dGetRadius(),n_Const::c_Convert::enGreaterEqual),1.0e-8)
            {
                CAssignment assignTemp;
                if(szMinimumDistanceCircle(pointInitial,pointFinal,
                                            *itTurnInitial,*itTurnFinal,assignTemp,
                                            dCommandSpeed_mps,dMinimumWaypointSeparation_m))
                {
                    //TODO:: ERROR!!!
                } 
                else
                {
                    // compare to find minimum distance
                    if((assignTemp.dGetDistanceTotal()) < dDistanceTotalMinimum_m)
                    {
                        assignMinimum = assignTemp;
                        dDistanceTotalMinimum_m = assignTemp.dGetDistanceTotal();
                    }
                }    //if(szMinimumDistanceCircle(pointInitial,pointFinal,*itTurnInitial,*itTurnFinal,assignTemp);)
            }    //if((itTurnInitial->turnGetTurnDirection() == itTurnFinal->turnGetTurnDirection())|| ....
            //check to see if "turn-turn-turn" is possible
            if(itTurnInitial->turnGetTurnDirection() == itTurnFinal->turnGetTurnDirection())
            {
                double dNorthSquared = pow((pointFinal.m_north_m - pointInitial.m_north_m),2.0);
                double dEast = pointFinal.m_east_m - pointInitial.m_east_m;
                double bTurnTurnTurnCheck1 = pow(dNorthSquared + pow((dEast - itTurnInitial->dGetRadius()),2.0),0.5);
                double bTurnTurnTurnCheck2 = pow(dNorthSquared + pow(dEast + itTurnInitial->dGetRadius(),2.0),0.5);
                double dDistanceCenters = itTurnInitial->relativeDistance2D_m(*itTurnFinal);

                if(n_Const::c_Convert::bCompareDouble(dDistanceCenters,(4.0*itTurnInitial->dGetRadius()),n_Const::c_Convert::enLessEqual)&&
                    ((bTurnTurnTurnCheck1<3.0*itTurnInitial->dGetRadius())||(bTurnTurnTurnCheck2<3.0*itTurnInitial->dGetRadius())))
                {
                    CAssignment assignTemp;
                    if(szMinimumDistanceTurnTurnTurn(pointInitial,pointFinal,
                                                        *itTurnInitial,*itTurnFinal,assignTemp,
                                                        dCommandSpeed_mps,dMinimumWaypointSeparation_m))
                    {
                        //TODO:: ERROR!!!
                    }
                    else
                    {
                        // compare to find minimum distance
                        if(n_Const::c_Convert::bCompareDouble(assignTemp.dGetDistanceTotal(),dDistanceTotalMinimum_m,n_Const::c_Convert::enLess))
                        {
                            assignMinimum = assignTemp;
                            dDistanceTotalMinimum_m = assignTemp.dGetDistanceTotal();
                        }
                    }    //if(szMinimumDistanceTurnTurnTurn(pointInitial,pointFinal,*itTurnInitial,*itTurnFinal,assignTemp))
                }        //if((bTurnTurnTurnCheck1<3.0*itTurnInitial->dGetRadius())||(bTurnTurnTurnCheck2<3.0*itTurnInitial->dGetRadius()))
            }    //if(itTurnInitial->turnGetTurnDirection() == circleSecond->turnGetTurnDirection())
        }    //for(int iCountSecondTurn=0;iCountSecondTurn<2;iCountSecondTurn++)
    }    //for(int iCountFirstTurn=0;iCountFirstTurn<2;iCountFirstTurn++)
    return(dDistanceTotalMinimum_m);
}



size_t CTrajectory::szMinimumDistanceCircle(CPosition posBegin,CPosition posEnd,
                                        CCircle& circleFirst,CCircle& circleSecond,
                                        CAssignment& rassignAssignment,
                                        const double& dCommandSpeed_mps,
                                        const double& dMinimumWaypointSeparation_m)
{

    //%  Probably ought to set these tolerances in the global defaults m-file
    double dAngleTol = 0.005;    //% If tangent point within angular tolerance to given point, use given point instead
    double dPositionTol = 0.01;    //% if turn circles centers are close together then consider them the same

    double dTheta_rad;
    double dDistCircleCenters = n_Const::c_Convert::iRound(circleSecond.relativeDistanceAngle2D_m(circleFirst,dTheta_rad));
    
    if(fabs(dDistCircleCenters) <= dPositionTol)
    {
        circleFirst = circleSecond;
        dDistCircleCenters = 0.0;
        dTheta_rad = 0.0;
    }

    CPosition posBeginSave = posBegin;
    posBegin.TransformPoint2D(circleFirst,-dTheta_rad);
    CPosition posEndSave = posEnd;
    posEnd.TransformPoint2D(circleFirst,-dTheta_rad);
    CPosition posSecondCenter = circleSecond;
    posSecondCenter.TransformPoint2D(circleFirst,-dTheta_rad);

    //%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
    //% find out if this should be a direct tangent or a transverse tanget
    //%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
    if(dDistCircleCenters < n_Const::c_Convert::iRound(circleFirst.dGetRadius() + circleSecond.dGetRadius()))
    {
       if((circleFirst.turnGetTurnDirection() != circleSecond.turnGetTurnDirection())||
            ((circleFirst.turnGetTurnDirection() == CCircle::turnNone) || (circleSecond.turnGetTurnDirection() == CCircle::turnNone))
            )
       {
           //TODO::ERROR (also do i need to check for 0 directions????
          return(errorWrongDirectionsForTangent);
       }
    }
    //%vehicle orienintation with initial circle
    double dAlpha = n_Const::c_Convert::dNormalizeAngleRad(atan2(posBegin.m_north_m,posBegin.m_east_m),0.0);
    //%desired final orientation angle
    double dBeta = n_Const::c_Convert::dNormalizeAngleRad(atan2((posEnd.m_north_m-posSecondCenter.m_north_m),(posEnd.m_east_m-posSecondCenter.m_east_m)),0.0);

    CPosition posTranversePoint1(0.0,0.0,posBegin.m_altitude_m);
    CPosition posTranversePoint2(0.0,0.0,posBegin.m_altitude_m);
    double dAlphaStar = 0.0;
    double dBetaStar = 0.0;

    //% AlphaStar is the angle of the tangent point on the initial turn circle
    if (circleFirst.turnGetTurnDirection() == circleSecond.turnGetTurnDirection())
    {
       //%use direct tangets
           if (circleSecond.turnGetTurnDirection() == CCircle::turnCounterclockwise)
        {
            //%bottom direct
            dAlphaStar = 1.5*n_Const::c_Convert::dPi();
            dBetaStar = 1.5*n_Const::c_Convert::dPi();
            posTranversePoint1.m_east_m = 0.0;
            posTranversePoint1.m_north_m = -circleFirst.dGetRadius();
            posTranversePoint2.m_east_m = dDistCircleCenters;
            posTranversePoint2.m_north_m = -circleSecond.dGetRadius();
        }
           else
        {
            //%top direct
            posTranversePoint1.m_east_m = 0.0;
            posTranversePoint1.m_north_m = circleFirst.dGetRadius();
            posTranversePoint2.m_east_m = dDistCircleCenters;
            posTranversePoint2.m_north_m = circleSecond.dGetRadius();
            dAlphaStar = 0.5*n_Const::c_Convert::dPi();
            dBetaStar = 0.5*n_Const::c_Convert::dPi();
        }
    }
    else    //if (circleFirst.turnGetTurnDirection() == circleSecond.turnGetTurnDirection())
    {
        //%use indirect tangets
        double dRatio = 2.0*circleFirst.dGetRadius()/dDistCircleCenters;
        if(n_Const::c_Convert::bCompareDouble(dRatio,1.0,n_Const::c_Convert::enLess,1.0e-3))
        {
            dAlphaStar = n_Const::c_Convert::dNormalizeAngleRad(acos(dRatio),0.0);
        }
        else
        {
            dAlphaStar = 0.0;
        }


        double dTangetNorth = circleFirst.dGetRadius() * sin(dAlphaStar);
        double dTangetEast = circleFirst.dGetRadius() * cos(dAlphaStar);
        if (circleSecond.turnGetTurnDirection() == CCircle::turnCounterclockwise)
        {
          //%top (negative slope) transverse
            posTranversePoint1.m_north_m = dTangetNorth;
            posTranversePoint1.m_east_m = dTangetEast;
            posTranversePoint2.m_north_m = -dTangetNorth;
            posTranversePoint2.m_east_m = dDistCircleCenters-dTangetEast;
        }
        else
        {
          //%bottom (positive slope) transverse
            posTranversePoint1.m_north_m = -dTangetNorth;
            posTranversePoint1.m_east_m = dTangetEast;
            posTranversePoint2.m_north_m = dTangetNorth;
            posTranversePoint2.m_east_m = dDistCircleCenters-dTangetEast;
            dAlphaStar = n_Const::c_Convert::dNormalizeAngleRad(n_Const::c_Convert::dTwoPi() - dAlphaStar,0.0);
        }
        dBetaStar = n_Const::c_Convert::dNormalizeAngleRad(dAlphaStar + n_Const::c_Convert::dPi(),0.0);
    }    //if (circleFirst.turnGetTurnDirection() == circleSecond.turnGetTurnDirection())


    //%Prevent going around too much of a circle
    double dAlphaDist = fabs(dAlphaStar - dAlpha);
    if ((dAlphaDist < dAngleTol) || (fabs(dAlphaDist - n_Const::c_Convert::dTwoPi()) < dAngleTol))
    {
        dAlphaStar = dAlpha;
    }
    double dBetaDist = fabs(dBetaStar - dBeta);
    if ((dBetaDist < dAngleTol) || (fabs(dBetaDist - n_Const::c_Convert::dTwoPi()) < dAngleTol))
    {
        dBetaStar = dBeta;
    }


    //%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
    //%% Distance calculation
    //%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
    // first turn
    double dDistance1 = 0.0;
    double dTurnRadius_m = circleFirst.dGetRadius();
    double dAngle01 = 0.0;
    if (circleFirst.turnGetTurnDirection() == CCircle::turnClockwise)
    {
        if(dAlpha >= dAlphaStar)
        {
            dAngle01 = dAlpha - dAlphaStar;
        }
        else
        {
            dAngle01 = dAlpha +(n_Const::c_Convert::dTwoPi() - dAlphaStar);
        }
    }
    else    //(circleFirst.turnGetTurnDirection() == CCircle::turnCounterclockwise)
    {
        if(dAlpha <= dAlphaStar)
        {
            dAngle01 = dAlphaStar - dAlpha;
        }
        else
        {
            dAngle01 = (n_Const::c_Convert::dTwoPi() - dAlpha) + dAlphaStar;
        }
    }    //(circleFirst.turnGetTurnDirection() == CCircle::turnCounterclockwise)
    dDistance1 = dAngle01*dTurnRadius_m;

    // straight segement
    double dDistance2 = posTranversePoint2.relativeDistance2D_m(posTranversePoint1);

    // second turn
    double dDistance3 = 0.0;
    double dAngle02 = 0.0;
    dTurnRadius_m = circleSecond.dGetRadius();
    if (circleSecond.turnGetTurnDirection() == CCircle::turnClockwise)
    {
        if(dBetaStar >= dBeta)
        {
            dAngle02 = dBetaStar - dBeta;
        }
        else
        {
            dAngle02 = dBetaStar + (n_Const::c_Convert::dTwoPi() - dBeta);
        }
    }
    else        //if (circleSecond.turnGetTurnDirection() == CCircle::turnCounterclockwise)
    {
        if(dBetaStar <= dBeta)
        {
            dAngle02 =  dBeta - dBetaStar;
        }
        else
        {
            dAngle02 = (n_Const::c_Convert::dTwoPi() - dBetaStar) + dBeta;
        }
    }    //if (circleSecond.turnGetTurnDirection() == CCircle::turnCounterclockwise)
    dDistance3 = dAngle02*dTurnRadius_m;


    //%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
    //%% transform waypoints back to original coordinate frame
    //%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
    posTranversePoint1.ReTransformPoint2D(circleFirst,-dTheta_rad);
    posTranversePoint2.ReTransformPoint2D(circleFirst,-dTheta_rad);

    //%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
    //%% add final waypoints to the vector for return
    //%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

    if(dDistance1 >= 1.0)    //TODO:: what value goes here????
    {
        posTranversePoint1.m_altitude_m = posBegin.m_altitude_m;
        AddWaypointsForTurn(posBeginSave,
                            posTranversePoint1,
                            dDistance1,
                            circleFirst,
                            circleFirst.dGetRadius(),
                            circleFirst.turnGetTurnDirection(),
                            dMinimumWaypointSeparation_m,
                            dCommandSpeed_mps,
                            rassignAssignment);
    }        //if(dDistance3 >= 10.0)    //TODO:: what value goes here????


#ifdef _ADD_EXTRA_WAYPOINT_IN_LINE


    rvwayWaypoint.push_back
        (
                CWaypoint
                (
                    (posTranversePoint2.m_north_m - posTranversePoint1.m_north_m)/2.0 + posTranversePoint1.m_north_m,
                    (posTranversePoint2.m_east_m - posTranversePoint1.m_east_m)/2.0 + posTranversePoint1.m_east_m,
                    posBegin.m_altitude_m,
                    dCommandSpeed_mps,false,
                    dDistance2/2.0,
                    std::numeric_limits<double>::max(),std::numeric_limits<double>::max(),std::numeric_limits<double>::max(),CCircle::turnNone
                )
        );
    double reSegmentTime_sec = (dCommandSpeed_mps<=0.0)?(std::numeric_limits<double>::max()):((dDistance2/2.0)/dCommandSpeed_mps);
    rvwayWaypoint.back().reGetSegmentTime() = reSegmentTime_sec;

    rvwayWaypoint.push_back
        (
                CWaypoint
                (
                    posTranversePoint2.m_north_m,posTranversePoint2.m_east_m,posBegin.m_altitude_m,
                    dCommandSpeed_mps,false,
                    dDistance2/2.0,
                    std::numeric_limits<double>::max(),std::numeric_limits<double>::max(),std::numeric_limits<double>::max(),CCircle::turnNone
                )
        );
    rvwayWaypoint.back().reGetSegmentTime() = reSegmentTime_sec;
#else    //#ifdef _ADD_EXTRA_WAYPOINT_IN_LINE

    rassignAssignment.iAddWaypoint
        (
                CWaypoint
                (
                    posTranversePoint2.m_north_m,posTranversePoint2.m_east_m,posBegin.m_altitude_m,
                    dCommandSpeed_mps,false,
                    dDistance2,
                    std::numeric_limits<double>::max(),std::numeric_limits<double>::max(),std::numeric_limits<double>::max(),CCircle::turnNone
                )
        );
    double reSegmentTime_sec = (dCommandSpeed_mps<=0.0)?(std::numeric_limits<double>::max()):(dDistance2/dCommandSpeed_mps);
    rassignAssignment.vwayGetWaypoints().back().reGetSegmentTime() = reSegmentTime_sec;
#endif    //#ifdef _ADD_EXTRA_WAYPOINT_IN_LINE

    if(dDistance3 >= 1.0)    //TODO:: what value goes here????
    {
        posTranversePoint2.m_altitude_m = posBegin.m_altitude_m;
        posEndSave.m_altitude_m = posBegin.m_altitude_m;
        AddWaypointsForTurn(posTranversePoint2,
                        posEndSave,
                        dDistance3,
                            circleSecond,
                            circleSecond.dGetRadius(),
                            circleSecond.turnGetTurnDirection(),
                            dMinimumWaypointSeparation_m,
                            dCommandSpeed_mps,
                            rassignAssignment);
    }        //if(dDistance3 >= 10.0)    //TODO:: what value goes here????

    rassignAssignment.SetNumberAssignments(1);

    return(errorNone);
}


size_t CTrajectory::szMinimumDistanceTurnTurnTurn(CPosition posBegin,CPosition posEnd,
                        CCircle& circleFirst,CCircle& circleSecond,CAssignment& rassignAssignment,
                                        const double& dCommandSpeed_mps,
                        const double& dMinimumWaypointSeparation_m)
{

    double dTurnRadius_m = circleFirst.dGetRadius();
    double dDistanceCenters = circleFirst.relativeDistance2D_m(circleSecond);

    double dGama = acos(dDistanceCenters/(4.0*dTurnRadius_m));

    double dDistanceA = std::numeric_limits<double>::max();    //%defaults to error condition
    double dDistanceB = (n_Const::c_Convert::dPi() + (2.0*dGama))*dTurnRadius_m;
    double dDistanceC = std::numeric_limits<double>::max();    //%defaults to error condition


    //%  Probably ought to set these tolerances in the global defaults m-file
    double dPositionTol = 0.01;    //% if turn circles centers are close together then consider them the same

    double dTheta_rad = 0.0;
    double dDistCircleCenters = circleSecond.relativeDistanceAngle2D_m(circleFirst,dTheta_rad);
    
    if(fabs(dDistCircleCenters) <= dPositionTol)
    {
        circleFirst = circleSecond;
        dDistCircleCenters = 0.0;
        dTheta_rad = 0.0;
    }

    CPosition posBeginSave = posBegin;
    posBegin.TransformPoint2D(circleFirst,-dTheta_rad);
    CPosition posEndSave = posEnd;
    posEnd.TransformPoint2D(circleFirst,-dTheta_rad);
    CPosition posSecondCenter = circleSecond;
    posSecondCenter.TransformPoint2D(circleFirst,-dTheta_rad);


    double dAlpha = n_Const::c_Convert::dNormalizeAngleRad(atan2(posBegin.m_north_m,posBegin.m_east_m),0.0);
    //%desired final orientation angle
    double dBeta = n_Const::c_Convert::dNormalizeAngleRad(atan2((posEnd.m_north_m-posSecondCenter.m_north_m),(posEnd.m_east_m-posSecondCenter.m_east_m)),0.0);

    CPosition posTangentPoint1(sin(dGama),cos(dGama),posBegin.m_altitude_m);
    posTangentPoint1 *= dTurnRadius_m;

    CPosition posTangentPoint2(sin(dGama),-cos(dGama),posBegin.m_altitude_m);
    posTangentPoint2 *= dTurnRadius_m;
    posTangentPoint2 += posSecondCenter;

    CPosition posTurnCenter(sin(dGama),cos(dGama));
    posTurnCenter *= 2.0*dTurnRadius_m;

    // move center of second turn down if clockwize
    if (circleFirst.turnGetTurnDirection() == CCircle::turnClockwise)
    {
        posTangentPoint1.m_north_m *= -1;
        posTangentPoint2.m_north_m *= -1;
        posTurnCenter.m_north_m *= -1;
    }


    //%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
    //%% Distance calculation
    //%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
    if (circleFirst.turnGetTurnDirection() == CCircle::turnCounterclockwise)
    {
        dDistanceA = (dAlpha<=dGama)?((dGama-dAlpha)*dTurnRadius_m):
                                            ((n_Const::c_Convert::dTwoPi()+dGama-dAlpha)*dTurnRadius_m);
        dDistanceC = (dBeta<=(n_Const::c_Convert::dPi()-dGama))?((n_Const::c_Convert::dPi()+dBeta+dGama)*dTurnRadius_m):
                                            ((dBeta+dGama-n_Const::c_Convert::dPi())*dTurnRadius_m);
    }
    else    //(circleFirst.turnGetTurnDirection() == CCircle::turnCounterclockwise)
    {
        dDistanceA = (dAlpha<=(n_Const::c_Convert::dTwoPi()-dGama))?((dGama+dAlpha)*dTurnRadius_m):
                                            ((dGama+dAlpha-n_Const::c_Convert::dTwoPi())*dTurnRadius_m);
        dDistanceC = (dBeta<=(n_Const::c_Convert::dPi()+dGama))?((n_Const::c_Convert::dPi()+dGama-dBeta)*dTurnRadius_m):
                                            ((3.0*n_Const::c_Convert::dPi()+dGama-dBeta)*dTurnRadius_m);
    }    //(circleFirst.turnGetTurnDirection() == CCircle::turnCounterclockwise)

    //%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
    //%% transform waypoints back to original coordinate frame
    //%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
    posTangentPoint1.ReTransformPoint2D(circleFirst,-dTheta_rad);
    posTangentPoint2.ReTransformPoint2D(circleFirst,-dTheta_rad);
    posTurnCenter.ReTransformPoint2D(circleFirst,-dTheta_rad);

    CCircle::enTurnDirection_t turnDirection = (circleFirst.turnGetTurnDirection()==CCircle::turnCounterclockwise)?(CCircle::turnClockwise):(CCircle::turnCounterclockwise);

    //%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
    //%% add final waypoints to the vector for return
    //%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

    AddWaypointsForTurn(posBeginSave,
                        posTangentPoint1,
                        dDistanceA,
                        circleFirst,
                        circleFirst.dGetRadius(),
                        circleFirst.turnGetTurnDirection(),
                        dMinimumWaypointSeparation_m,
                        dCommandSpeed_mps,
                        rassignAssignment);


    AddWaypointsForTurn(posTangentPoint1,
                        posTangentPoint2,
                        dDistanceB,
                        posTurnCenter,
                        dTurnRadius_m,
                        turnDirection,
                        dMinimumWaypointSeparation_m,
                        dCommandSpeed_mps,
                        rassignAssignment);


    AddWaypointsForTurn(posTangentPoint2,
                        posEndSave,
                        dDistanceC,
                        circleSecond,
                        dTurnRadius_m,
                        circleSecond.turnGetTurnDirection(),
                        dMinimumWaypointSeparation_m,
                        dCommandSpeed_mps,
                        rassignAssignment);


    rassignAssignment.SetNumberAssignments(1);
    return(errorNone);
}



void CTrajectory::AddWaypointsForTurn(CPosition& posStart,
                                    const CPosition& posEnd,
                                    const double& dArcLength,
                                    CPosition& posCenter,
                                    const double& dRadius,
                                    const CCircle::enTurnDirection_t& turnDirection,
                                    const double& bMinimumSeparation,
                                    const double& dCommandSpeed_mps,
                                    CAssignment& cAssignment)
{
    double dTotalDistanceTraveled = 0.0;    //distance used by adding new waypoints
    int iNumberIncrements = 0;
    double dAngleIncrement_rad = 0.0;

    //mark waypoint at start of turn so it does not get removed
    if(!cAssignment.vwayGetWaypoints().empty())
    {
        cAssignment.vwayGetWaypoints().back().bGetDoNotRemove() = true;
    }

    if((dRadius > 0.0)&&(turnDirection!=CCircle::turnNone)&&(dArcLength > bMinimumSeparation))
    {
        double dTotalAngle_rad = dArcLength/dRadius;
        dAngleIncrement_rad = bMinimumSeparation/dRadius;
        iNumberIncrements = (dAngleIncrement_rad == 0.0)?(0):(static_cast<int>(dTotalAngle_rad/dAngleIncrement_rad));
        dAngleIncrement_rad *= (double)turnDirection;

        if(iNumberIncrements > 0)
        {
            int iMiddlePointIncrement = iNumberIncrements/2;
            iMiddlePointIncrement = (iMiddlePointIncrement<=1)?(-1):(iMiddlePointIncrement);

            //posCenter.reGetAltitude_m() = 0.0;

            double dAngleStart_rad = posStart.relativeAngle2D_rad(posCenter);
            int iTotalIncrements = 1;
            double dAnglePoint_rad = dAngleIncrement_rad + dAngleStart_rad;

            while(iTotalIncrements < iNumberIncrements)
            {
                CPosition posTemp(dRadius*sin(dAnglePoint_rad),dRadius*cos(dAnglePoint_rad),posStart.m_altitude_m);

                posTemp += posCenter;
                cAssignment.iAddWaypoint
                (
                        CWaypoint
                        (
                        posTemp,dCommandSpeed_mps,false,bMinimumSeparation,
                            posCenter.m_north_m,posCenter.m_east_m,dRadius,turnDirection
                        )
                );
                if(iTotalIncrements == iMiddlePointIncrement)
                {
                    cAssignment.vwayGetWaypoints().back().bGetDoNotRemove() = true;
                }
                double reSegmentTime_sec = (dCommandSpeed_mps<=0.0)?(std::numeric_limits<double>::max()):(bMinimumSeparation/dCommandSpeed_mps);
                cAssignment.vwayGetWaypoints().back().reGetSegmentTime() = reSegmentTime_sec;

                dTotalDistanceTraveled += bMinimumSeparation;
                dAnglePoint_rad += dAngleIncrement_rad;
                iTotalIncrements++;
            }        //while(iTotalIncrements < iNumberIncrements)
        }    //if(iNumberIncrements > 0)
    }    //if((dRadius > 0.0)&&(turnDirection!=CCircle::turnNone))

    //add final waypoint to turn
    double dDistanceTraveledFinal = (dTotalDistanceTraveled > dArcLength)?(0.0):(dArcLength - dTotalDistanceTraveled);

//cout<< dDistanceTraveledFinal << "\t" << dArcLength << "\t" << iNumberIncrements << "\t" << dAngleIncrement_rad << "\t" <<endl;

    cAssignment.iAddWaypoint
    (
        CWaypoint(posEnd.m_north_m,posEnd.m_east_m,posEnd.m_altitude_m,
                    dCommandSpeed_mps,false,dDistanceTraveledFinal,
                    posCenter.m_north_m,posCenter.m_east_m,dRadius,turnDirection)
    );
    double reSegmentTime_sec = (dCommandSpeed_mps<=0.0)?(std::numeric_limits<double>::max()):(dDistanceTraveledFinal/dCommandSpeed_mps);
    //mark waypoint at end of turn so it does not get removed
    cAssignment.vwayGetWaypoints().back().bGetDoNotRemove() = true;
    cAssignment.vwayGetWaypoints().back().reGetSegmentTime() = reSegmentTime_sec;
}


};      //namespace n_FrameworkLib
