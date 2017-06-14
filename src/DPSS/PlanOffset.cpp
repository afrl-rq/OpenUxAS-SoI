// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#include "Dpss.h"
using namespace std;

void Dpss::OffsetPlanForward(std::vector<xyPoint> &xyPlanPoints, std::vector<xyPoint> &forwardPlan)
{
    RemoveZeroLengthSegments(xyPlanPoints);
    forwardPlan.clear();

    // handle nonsense input
    if(xyPlanPoints.empty()) return;
    if(xyPlanPoints.size() == 1)
    {
        forwardPlan.push_back(xyPlanPoints[0]);
        return;
    }

    //if(!m_TerrainFollowing)
    //    PrintRoadXYZ("roadInMeters.m", xyPlanPoints);

    int len = (int) xyPlanPoints.size();
    for(int k=0; k < len; k++)
    {
        double d;

        // distance offset calculation
        if( m_NominalElevation < 1.0*dDeg2Rad || m_NominalElevation > 89.0*dDeg2Rad )
            d = 0;
        else
        {
            if(!m_TerrainFollowing)
                d = (m_NominalAltitudeInMeters - xyPlanPoints[k].z)/tan(m_NominalElevation);
            else
                d = m_NominalAltitudeInMeters/tan(m_NominalElevation);
            if( (k!=(len-1)) && (k!=0) ) d *= sin(m_NominalAzimuth);
        }

        xyPoint v = (k==0)?(xyPlanPoints[1] - xyPlanPoints[0]):(xyPlanPoints[k] - xyPlanPoints[k-1]); 
        double th;
        if( (k==0) || (k==(len-1)))
            th = dPi - m_NominalAzimuth;
        else
        {
            ComputeSeperation(th,xyPlanPoints[k-1],xyPlanPoints[k],xyPlanPoints[k+1]);
            th = (dPi - th)/2.0;
        }
        v.Rotate(th); // counter clockwise rotation
        if(v.len() > 1e-10)
            v *= d/v.len();
        v += xyPlanPoints[k];
        v.attributes = xyPlanPoints[k].attributes;
        forwardPlan.push_back(v);
    }

    RemoveZeroLengthSegments(forwardPlan);
    CleanUpStareAngles(forwardPlan, m_PlanningRoad);
    RemoveZeroLengthSegments(forwardPlan);

}

void Dpss::OffsetPlanReverse(std::vector<xyPoint> &xyPlanPoints, std::vector<xyPoint> &reversePlan)
{
    RemoveZeroLengthSegments(xyPlanPoints);
    reversePlan.clear();

    // handle nonsense input
    if(xyPlanPoints.empty()) return;
    if(xyPlanPoints.size() == 1) return;

    int len = (int) xyPlanPoints.size();
    double az = m_NominalAzimuth;
    if(m_SameSidePlan) az = -az;

    for(int k=(len-1); k >= 0; k--)
    {
        double d;

        // distance offset calculation
        if( m_NominalElevation < 1.0*dDeg2Rad || m_NominalElevation > 89.0*dDeg2Rad )
            d = 0;
        else
        {
            if(!m_TerrainFollowing)
                d = (m_NominalAltitudeInMeters - xyPlanPoints[k].z)/tan(m_NominalElevation);
            else
                d = m_NominalAltitudeInMeters/tan(m_NominalElevation);
            if( (k!=(len-1)) && (k!=0) ) d *= sin(m_NominalAzimuth);
        }

        xyPoint v = (k==(len-1))?(xyPlanPoints[len-2] - xyPlanPoints[len-1]):(xyPlanPoints[k] - xyPlanPoints[k+1]);
        double th;
        if( (k==0) || (k==(len-1)))
            th = dPi - az;
        else
        {
            ComputeSeperation(th,xyPlanPoints[k+1],xyPlanPoints[k],xyPlanPoints[k-1]);
            // rotation of -th will align vectors
            th = (dPi - th)/2.0;
            if(m_SameSidePlan)
                d *= -1.0;
        }
        v.Rotate(th);
        if(v.len() > 1e-10)
            v *= d/v.len();
        v += xyPlanPoints[k];

        reversePlan.push_back(v);
    }

    RemoveZeroLengthSegments(reversePlan);

    std::vector<xyPoint> tempPlan;
    tempPlan.clear();
    len = (int)reversePlan.size();
    for(int n=0; n<len; n++)
        tempPlan.push_back(reversePlan[len-n-1]);

    CleanUpStareAngles(tempPlan, m_PlanningRoad);

    reversePlan.clear();
    len = (int)tempPlan.size();
    for(int m=0; m<len; m++)
        reversePlan.push_back(tempPlan[len-m-1]);

    RemoveZeroLengthSegments(reversePlan);
}

void Dpss::CombinePlans(std::vector<xyPoint> &forwardPlan, std::vector<xyPoint> &reversePlan, DpssWaypoint* outputPoints, int* numOutputPoints)
{
    int k;
    int numForward = (int) forwardPlan.size();
    int numReverse = (int) reversePlan.size();
    *numOutputPoints = numForward+numReverse;
    
    for(k=0; k < numForward; k++)
    {
        m_FlatEarthConverter.ConvertNorthEast_mToLatLong_rad(forwardPlan[k].y, forwardPlan[k].x, outputPoints[k].latitudeInRadians, outputPoints[k].longitudeInRadians);
        outputPoints[k].waypointNumber = (unsigned short) (k+1);
        outputPoints[k].altitudeInMeters = m_NominalAltitudeInMeters;
    }

    for(k=0; k < numReverse; k++)
    {
        m_FlatEarthConverter.ConvertNorthEast_mToLatLong_rad(reversePlan[k].y, reversePlan[k].x, outputPoints[k+numForward].latitudeInRadians, outputPoints[k+numForward].longitudeInRadians);
        outputPoints[k+numForward].waypointNumber = (unsigned short) (k+numForward+1);
        outputPoints[k+numForward].altitudeInMeters = m_NominalAltitudeInMeters;
    }
}

void Dpss::CleanUpStareAngles(std::vector<xyPoint>& plan, std::vector<xyPoint>& road)
{
    int k;
    std::vector<xyPoint> starePoints;
    CorrespondingStarePoints(plan, road, starePoints);
        
        if(plan.size() < 3)
            return;

    // throw out adjacent crossing look angles
    bool lookAnglesCrossing;
    do{
        lookAnglesCrossing = false;
        for(k=1; k<(int)plan.size(); k++)
        {
            Segment s(plan[k],starePoints[k]);
            Segment r(plan[k-1], starePoints[k-1]);
            if(s.len() > 1e-4 && r.len() > 1e-4)
            {
                xyPoint intersection = s.intersectPoint(r);
                lookAnglesCrossing = (s.intersect(r)) && (intersection.z < 0.0);
                lookAnglesCrossing = lookAnglesCrossing || ( (s.swathSide(intersection) == 0) && (r.swathSide(intersection) == 0) );
            }

            if(lookAnglesCrossing)
                break;
        }

        if(lookAnglesCrossing)
        {
            if(k == ((int) plan.size()-1) )
                k--;
            xyPoint p = (plan[k-1] + plan[k])/2;
            vector<xyPoint>::iterator q = plan.begin() + k;
            plan.erase(q);
            plan[k-1] = p;
            CorrespondingStarePoints(plan, road, starePoints);
        }
    }while( lookAnglesCrossing && (plan.size() >= 3) );
}

void Dpss::CorrespondingStarePoints(std::vector<xyPoint>& plan, std::vector<xyPoint>& road, std::vector<xyPoint>& starePoints)
{
    int k;

    // plan length
    double totalPlanLength = 0.0;
    for(k=1; k<(int)plan.size(); k++)
    {
        Segment s(plan[k-1],plan[k]);
        totalPlanLength += s.len();
    }

    // road length
    double totalRoadLength = 0.0;
    for(k=1; k<(int)road.size(); k++)
    {
        Segment s(road[k-1],road[k]);
        totalRoadLength += s.len();
    }

    starePoints.clear();
    starePoints.push_back(road[0]);

    double lengthCovered = 0.0;
    for(k=1; k<(int)plan.size()-1; k++)
    {
        Segment s(plan[k-1],plan[k]);
        lengthCovered += s.len();

        xyPoint starePoint;

        double correspondingRoadLength = lengthCovered/totalPlanLength*totalRoadLength;
        double roadCovered = 0.0;
        for(int n=1; n<(int)road.size(); n++)
        {
            Segment r(road[n-1],road[n]);
            if( (roadCovered+r.len()) > correspondingRoadLength)
            {
                if(r.len() > 1e-6)
                    starePoint = road[n-1] + (road[n] - road[n-1])*((correspondingRoadLength-roadCovered)/r.len());
                else
                    starePoint = road[n-1];
                break;
            }
            roadCovered += r.len();
        }
        
        starePoints.push_back(starePoint);
    }
    starePoints.push_back(road[ (int)road.size() - 1 ]);
}
