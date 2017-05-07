// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#include "Dpss.h"
#include <algorithm>
#include <functional>
#include <iostream>
#include <fstream>
using namespace std;

void Dpss::CalculateStarePoint(VehiclePoint &starePoint, VehicleTelemetry &vehiclePosition)
{
    // default values (nadir view)
    starePoint.altitudeInMeters = vehiclePosition.altitudeInMeters - m_NominalAltitudeInMeters;
    starePoint.latitudeInRadians = vehiclePosition.latitudeInRadians;
    starePoint.longitudeInRadians = vehiclePosition.longitudeInRadians;
    starePoint.vehicleId = vehiclePosition.vehicleId;

    double normalizedPt = CorrespondingNormalizedRoadLocation(vehiclePosition);
    if(normalizedPt < 0.0)
        return;

    if(normalizedPt == 1.0)
    {
        int lastPt = ( (int) m_TrueRoad.size() ) - 1;
        starePoint.altitudeInMeters = m_TrueRoad[lastPt].z;
        m_FlatEarthConverter.ConvertNorthEast_mToLatLong_rad(m_TrueRoad[lastPt].y, m_TrueRoad[lastPt].x, starePoint.latitudeInRadians, starePoint.longitudeInRadians);
        starePoint.vehicleId = vehiclePosition.vehicleId;
        return;
    }

    if(normalizedPt == 0.0)
    {
        starePoint.altitudeInMeters = m_TrueRoad[0].z;
        m_FlatEarthConverter.ConvertNorthEast_mToLatLong_rad(m_TrueRoad[0].y, m_TrueRoad[0].x, starePoint.latitudeInRadians, starePoint.longitudeInRadians);
        starePoint.vehicleId = vehiclePosition.vehicleId;
        return;
    }

    xyPoint p;
    NormalizedRoadPosToXyRoadPos(p,normalizedPt);

    starePoint.altitudeInMeters = p.z;
    m_FlatEarthConverter.ConvertNorthEast_mToLatLong_rad(p.y, p.x, starePoint.latitudeInRadians, starePoint.longitudeInRadians);
    starePoint.vehicleId = vehiclePosition.vehicleId;
}

void Dpss::CalculateStarePoint(xyPoint &starePoint, xyPoint &vehiclePosition)
{
    // default values (nadir view)
    starePoint.z = vehiclePosition.z - m_NominalAltitudeInMeters;
    starePoint.x = vehiclePosition.x;
    starePoint.y = vehiclePosition.y;

    double normalizedPt = CorrespondingNormalizedRoadLocation(vehiclePosition);
    if(normalizedPt < 0.0)
        return;

    if(normalizedPt == 1.0)
    {
        int lastPt = ( (int) m_TrueRoad.size() ) - 1;
        starePoint.z = m_TrueRoad[lastPt].z;
        starePoint.x = m_TrueRoad[lastPt].x;
        starePoint.y = m_TrueRoad[lastPt].y;
        return;
    }

    if(normalizedPt == 0.0)
    {
        starePoint.z = m_TrueRoad[0].z;
        starePoint.x = m_TrueRoad[0].x;
        starePoint.y = m_TrueRoad[0].y;
        return;
    }

    NormalizedRoadPosToXyRoadPos(starePoint,normalizedPt);
}

void Dpss::CalculateWpToRdIndexMap()
{
    int k;

    m_RdIDList.clear();
    m_ReturnPlanWpIndex = 0;
    
    if(m_TrueWaypoints.empty() || m_TrueRoad.empty())
        return;

    // find turn around point: waypoint segment on which road endpoint is closest to midpoint
    double minDistToEnd = -1.0;
    for(k=1; k<(int)m_TrueWaypoints.size(); k++)
    {
        xyPoint midPoint = (m_TrueWaypoints[k-1] + m_TrueWaypoints[k])/2.0;
        midPoint -= m_TrueRoad[( (int) m_TrueRoad.size() ) - 1];
        double dist = midPoint.len();
        if(dist < minDistToEnd || minDistToEnd < 0.0)
        {
            minDistToEnd = dist;
            m_ReturnPlanWpIndex = k;
        }
    }

    if(m_SingleDirectionPlan)
        m_ReturnPlanWpIndex = (int) m_TrueWaypoints.size();

    m_ForwardPlanLength = 0.0;
    m_ReversePlanLength = 0.0;
    m_TrueRoadLength = 0.0;

    // forward length
    for(k=1; k<m_ReturnPlanWpIndex; k++)
    {
        Segment s(m_TrueWaypoints[k-1],m_TrueWaypoints[k]);
        m_ForwardPlanLength += s.len();
    }

    // reverse length
    for(k=m_ReturnPlanWpIndex+1; k<(int)m_TrueWaypoints.size(); k++)
    {
        Segment s(m_TrueWaypoints[k-1],m_TrueWaypoints[k]);
        m_ReversePlanLength += s.len();
    }

    // road length
    for(k=1; k<(int)m_TrueRoad.size(); k++)
    {
        Segment s(m_TrueRoad[k-1],m_TrueRoad[k]);
        m_TrueRoadLength += s.len();
    }

    // [0 .. 1] mapping for road
    m_TrueRoadLengths.push_back(0.0);
    for(k=1; k < ( ((int)m_TrueRoad.size()) - 1); k++)
    {
        Segment s(m_TrueRoad[k-1],m_TrueRoad[k]);
        m_TrueRoadLengths.push_back( m_TrueRoadLengths[k-1] + s.len()/m_TrueRoadLength );
    }
    m_TrueRoadLengths.push_back(1.0);

    // create forward search areas solution
    std::vector<double> forwardSolution;
    double lengthCovered = 0.0;
    for(k=1; k<m_ReturnPlanWpIndex-1; k++)
    {
        Segment s(m_TrueWaypoints[k-1],m_TrueWaypoints[k]);
        lengthCovered += s.len();
        double midPosition = lengthCovered/m_ForwardPlanLength;
        forwardSolution.push_back(midPosition);
    }

    // create constant reverse flow solution
    std::vector<double> reverseSolution;
    lengthCovered = 0.0;
    for(k=m_ReturnPlanWpIndex+1; k<(int)m_TrueWaypoints.size()-1; k++)
    {
        Segment s(m_TrueWaypoints[k-1],m_TrueWaypoints[k]);
        lengthCovered += s.len();
        double midPosition = 1.0 - lengthCovered/m_ReversePlanLength;
        reverseSolution.push_back(midPosition);
    }

    BuildConversionMappings(forwardSolution, reverseSolution);

    // recalculate mapping for updated m_TrueRoad
    m_TrueRoadLengths.clear();
    m_TrueRoadLengths.push_back(0.0);
    for(k=1; k < ( ((int)m_TrueRoad.size()) - 1); k++)
    {
        Segment s(m_TrueRoad[k-1],m_TrueRoad[k]);
        m_TrueRoadLengths.push_back( m_TrueRoadLengths[k-1] + s.len()/m_TrueRoadLength );
    }
    m_TrueRoadLengths.push_back(1.0);

    // ---- DEBUG ---- //
    FullDebugPlan();
    // ---- DEBUG ---- //

}

void Dpss::BuildConversionMappings(std::vector<double>& forwardSolution, std::vector<double>& reverseSolution)
{
    int k;

    // mapping for forward direction
    std::vector<double> forwardRoadTargets;
    //for(k=0; k<(int)forwardSolution.size(); k++)
    //    forwardRoadTargets.push_back(m_ForwardStartPositions[k] + forwardSolution[k]*(m_ForwardEndPositions[k] - m_ForwardStartPositions[k]));
    //sort(forwardRoadTargets.begin(), forwardRoadTargets.end());
    forwardRoadTargets.assign(forwardSolution.begin(), forwardSolution.end());
    
    // pin first mapping to road index 0, waypoint index 0
    m_RdIDList.push_back(0);

    for(k=1; k<m_ReturnPlanWpIndex-1; k++)
    {
        xyPoint starePoint;
        int rdIndx = 0;
        bool validStarePoint = false;

        double correspondingRoadLength = forwardRoadTargets[k-1]*m_TrueRoadLength;
        double roadCovered = 0.0;
        for(int n=1; n<(int)m_TrueRoad.size(); n++)
        {
            Segment r(m_TrueRoad[n-1],m_TrueRoad[n]);
            if( (roadCovered+r.len()) >= correspondingRoadLength)
            {
                rdIndx = n;
                if(r.len() > 1e-6)
                    starePoint = m_TrueRoad[n-1] + (m_TrueRoad[n] - m_TrueRoad[n-1])*((correspondingRoadLength-roadCovered)/r.len());
                else
                    starePoint = m_TrueRoad[n-1];
                validStarePoint = true;
                break;
            }
            roadCovered += r.len();
        }
        
        if(!validStarePoint)
        {
            rdIndx = (int)m_TrueRoad.size() - 1;
            starePoint = m_TrueRoad[rdIndx];
        }

        vector<xyPoint>::iterator insertRdPoint = m_TrueRoad.begin() + rdIndx;
        m_TrueRoad.insert(insertRdPoint,starePoint);
        m_RdIDList.push_back(rdIndx);
    }
    m_RdIDList.push_back( ((int)m_TrueRoad.size()) - 1 );


    if(!m_SingleDirectionPlan)
    {
        // mapping for reverse direction
        std::vector<double> reverseRoadTargets;
        //for(k=0; k<(int)reverseSolution.size(); k++)
        //    reverseRoadTargets.push_back(m_ReverseStartPositions[k] + reverseSolution[k]*(m_ReverseEndPositions[k] - m_ReverseStartPositions[k]));
        //sort(reverseRoadTargets.begin(), reverseRoadTargets.end(), greater<double>());
        reverseRoadTargets.assign(reverseSolution.begin(), reverseSolution.end());

        // pin first mapping to road index [end], waypoint index [m_ReturnPlanWpIndex]
        m_RdIDList.push_back( ((int)m_TrueRoad.size()) - 1 );

        for(k=m_ReturnPlanWpIndex+1; k<(int)m_TrueWaypoints.size()-1; k++)
        {
            xyPoint starePoint;
            int rdIndx = 0;
            bool validStarePoint = false;

            double correspondingRoadLength = (1.0-reverseRoadTargets[k-1-m_ReturnPlanWpIndex])*m_TrueRoadLength;
            double roadCovered = 0.0;
            for(int n=((int)m_TrueRoad.size())-1; n>0; n--)
            {
                Segment r(m_TrueRoad[n],m_TrueRoad[n-1]);
                if( (roadCovered+r.len()) >= correspondingRoadLength)
                {
                    rdIndx = n;
                    if(r.len() > 1e-6)
                        starePoint = m_TrueRoad[n] + (m_TrueRoad[n-1] - m_TrueRoad[n])*((correspondingRoadLength-roadCovered)/r.len());
                    else
                        starePoint = m_TrueRoad[n];
                    validStarePoint = true;
                    break;
                }
                roadCovered += r.len();
            }

            if(!validStarePoint)
            {
                rdIndx = 1;
                starePoint = m_TrueRoad[0];
            }
            
            // will muck up the list to insert a new stare point, adjust others in list to accommodate
            vector<xyPoint>::iterator insertRdPoint = m_TrueRoad.begin() + rdIndx;
            for(int m=0; m<(int) m_RdIDList.size(); m++)
                if(m_RdIDList[m] >= rdIndx)
                    m_RdIDList[m]++;
            m_TrueRoad.insert(insertRdPoint,starePoint);
            m_RdIDList.push_back(rdIndx);
        }
        m_RdIDList.push_back(0);
    }
}

double Dpss::SensorPointingCostForward(std::vector<double>& x)
{
    int k;
    double cost = 0.0;
    std::vector<double> y;
    for(k=0; k<(int)x.size(); k++)
        y.push_back(m_ForwardStartPositions[k] + x[k]*(m_ForwardEndPositions[k] - m_ForwardStartPositions[k]));
    sort(y.begin(), y.end());

    for(k=0; k<(int)y.size(); k++)
    {
        if(y[k] < 0.0)
            y[k] = 0.0;
        if(y[k] > 1.0)
            y[k] = 1.0;
    }

    for(k=1; k<m_ReturnPlanWpIndex-1; k++)
    {
        xyPoint p;
        double beta, desiredAz, actualAz;

        ComputeSeperation(beta, m_TrueWaypoints[k-1], m_TrueWaypoints[k], m_TrueWaypoints[k+1]);
        desiredAz = beta/2.0 + m_NominalAzimuth; // share angle between consecutive segments
        
        NormalizedRoadPosToXyRoadPos(p,y[k-1]);
        ComputeSeperation(actualAz, m_TrueWaypoints[k-1], m_TrueWaypoints[k], p);

        double angleDelta = actualAz - desiredAz;
        if(angleDelta >  dPi) angleDelta -= 2*dPi;
        if(angleDelta < -dPi) angleDelta += 2*dPi;
        cost += angleDelta*angleDelta;

        Segment s(m_TrueWaypoints[k-1],m_TrueWaypoints[k]);

        if(k == 1)
            cost += pow(dPi*m_EqualDistanceWeight*(y[k-1] - s.len()/m_ForwardPlanLength),2.0);
        else
            cost += pow(dPi*m_EqualDistanceWeight*(y[k-1] - y[k-2] - s.len()/m_ForwardPlanLength),2.0);
    }
    xyPoint q = m_TrueWaypoints[m_ReturnPlanWpIndex] - m_TrueWaypoints[m_ReturnPlanWpIndex-1];
    cost += pow(dPi*m_EqualDistanceWeight*(1.0 - y[(int) y.size()-1] - q.len()/m_ForwardPlanLength),2.0);

    return cost;
}

double Dpss::SensorPointingCostReverse(std::vector<double>& x)
{
    int k;
    double cost = 0.0;
    std::vector<double> y;
    for(k=0; k<(int)x.size(); k++)
        y.push_back(m_ReverseStartPositions[k] + x[k]*(m_ReverseEndPositions[k] - m_ReverseStartPositions[k]));
    sort(y.begin(), y.end(),greater<double>());

    for(k=0; k<(int)y.size(); k++)
    {
        if(y[k] < 0.0)
            y[k] = 0.0;
        if(y[k] > 1.0)
            y[k] = 1.0;
    }

    for(k=m_ReturnPlanWpIndex+1; k<(int)m_TrueWaypoints.size()-1; k++)
    {
        int yindex = k-1-m_ReturnPlanWpIndex;

        xyPoint p;
        double beta, desiredAz, actualAz;

        ComputeSeperation(beta, m_TrueWaypoints[k-1], m_TrueWaypoints[k], m_TrueWaypoints[k+1]);
        desiredAz = beta/2.0 + m_NominalAzimuth; // share angle between consecutive segments

        if(m_SameSidePlan) desiredAz -= 2*m_NominalAzimuth;
        
        NormalizedRoadPosToXyRoadPos(p,y[yindex]);
        ComputeSeperation(actualAz, m_TrueWaypoints[k-1], m_TrueWaypoints[k],p);

        double angleDelta = actualAz - desiredAz;
        if(angleDelta >  dPi) angleDelta -= 2*dPi;
        if(angleDelta < -dPi) angleDelta += 2*dPi;
        cost += angleDelta*angleDelta;

        Segment s(m_TrueWaypoints[k-1],m_TrueWaypoints[k]);
        if(yindex == 0)
            cost += pow(dPi*m_EqualDistanceWeight*(1.0 - y[yindex] - s.len()/m_ReversePlanLength),2.0);
        else
            cost += pow(dPi*m_EqualDistanceWeight*(y[yindex-1] - y[yindex] - s.len()/m_ReversePlanLength),2.0);
    }
    xyPoint q = m_TrueWaypoints[(int)m_TrueWaypoints.size()-1] - m_TrueWaypoints[(int)m_TrueWaypoints.size()-2];
    cost += pow(dPi*m_EqualDistanceWeight*(y[(int) y.size()-1] - q.len()/m_ReversePlanLength),2.0);

    return cost;
}
