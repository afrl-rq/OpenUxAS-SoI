// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#include "SegmentMap.h"

SegmentMap::SegmentMap()
{
    totalPlanLength = 0.0;
    totalPathLength = 0.0;
}

SegmentMap::SegmentMap(std::vector<xyPoint>& uavPlan, std::vector<xyPoint>& road)
{
    totalPlanLength = 0.0;
    totalPathLength = 0.0;
    Initialize(uavPlan, road);
}

SegmentMap::~SegmentMap()
{
    path.clear();
    plan.clear();
    normalizedPathLengths.clear();
}

void SegmentMap::Initialize(std::vector<xyPoint>& uavPlan, std::vector<xyPoint>& road)
{
    unsigned int n;
    Segment q;

    totalPlanLength = 0.0;
    totalPathLength = 0.0;

    path.assign(road.begin(), road.end());
    plan.assign(uavPlan.begin(), uavPlan.end());
    normalizedPathLengths.clear();

    for(n=0; n<(path.size()-1); n++)
    {
        q.a = path[n]; q.b = path[n+1];
        normalizedPathLengths.push_back(totalPathLength);
        totalPathLength += q.len();
    }
    for(n=0; n<normalizedPathLengths.size(); n++)
        normalizedPathLengths[n] /= totalPathLength;
    normalizedPathLengths.push_back(1.0);

    for(n=0; n<(plan.size()-1); n++)
    {
        q.a = plan[n]; q.b = plan[n+1];
        totalPlanLength += q.len();
    }
}

int SegmentMap::SnapToSegment(std::vector<xyPoint>& polyline, xyPoint& actualLocation, xyPoint& snappedLocation)
{
    if(polyline.empty())
        return -1;
    if(polyline.size() == 1)
    {
        snappedLocation = polyline[0];
        return 0;
    }

    Segment q(polyline[0],polyline[1]);
    double dist = q.distToClosestPoint(actualLocation);
    snappedLocation = q.closestPoint(actualLocation);
    int segmentIndex = 0;
    for(unsigned int n=1; n<(polyline.size()-1); n++)
    {
        q.a = polyline[n]; q.b = polyline[n+1];
        if(q.distToClosestPoint(actualLocation) < dist)
        {
            dist = q.distToClosestPoint(actualLocation);
            snappedLocation = q.closestPoint(actualLocation);
            segmentIndex = n;
        }
    }
    return segmentIndex;
}

xyPoint SegmentMap::CalculateStarePoint(xyPoint& uavLoc)
{
    Segment q;
    unsigned int n;

    // check nonsense inputs
    if(path.empty())
        return xyPoint(0,0,0);

    if(path.size() == 1 || plan.size() < 2)
        return path[0];
    
    if(totalPlanLength < 1e-6 || totalPathLength < 1e-6)
        return path[0];

    xyPoint snappedLoc;
    int segmentIndex = SnapToSegment(plan,uavLoc,snappedLoc);
    if(segmentIndex < 0)
        return path[0];

    // find percent along the uavPlan
    double uavPlanDistance = 0.0;
    for(n=0; n<(unsigned int) segmentIndex; n++)
    {
        q.a = plan[n]; q.b = plan[n+1];
        uavPlanDistance += q.len();
    }
    q.a = plan[segmentIndex]; q.b = plan[segmentIndex+1];
    uavPlanDistance += snappedLoc.dist(q.a);
    double uavPercentPlan = uavPlanDistance / totalPlanLength;

    // find corresponding path percentage
    for(n=0; n<(normalizedPathLengths.size()-1); n++)
    {
        if( normalizedPathLengths[n+1] >= uavPercentPlan )
        {
            q.a = path[n]; q.b = path[n+1];
            if(q.len() < 1e-6)
                return path[n];
            double distanceFromEndpoint = uavPercentPlan*totalPathLength - normalizedPathLengths[n];
            xyPoint v = q.b - q.a; v = v/q.len();
            xyPoint starePoint = q.a + v*distanceFromEndpoint;
            return starePoint;
        }
    }

    return path[path.size()-1];
}

// Compute a stare point using a piecewise linear uavPlan and
//   associated road. Endpoints of the uavPlan correspond to
//   endpoints of the road and percentage traveled along
//   uavPlan is used to find corresponding stare point
xyPoint SegmentMap::CalculateStarePoint(std::vector<xyPoint>& uavPlan, std::vector<xyPoint>& road, xyPoint& uavLoc)
{
    // This is a stand-alone function that uses no storage
    // to compute the stare point
    unsigned int n;
    Segment q;
    xyPoint uavPlanLocation;

    // check nonsense inputs
    if(road.empty())
        return xyPoint(0,0,0);

    if(road.size() == 1 || uavPlan.size() < 2)
        return road[0];

    // need to find closest segment for proper mapping
    // by checking distance to all segments on the uavPlan
    // for the closest one. Simultaneously, calculate
    // total length of the uavPlan
    double uavPlanLength = 0.0;
    for(n=0; n<(uavPlan.size()-1); n++)
    {
        q.a = uavPlan[n]; q.b = uavPlan[n+1];
        uavPlanLength += q.len();
    }

    // calculate total length of the road
    double roadLength = 0.0;
    for(n=0; n<(road.size()-1); n++)
    {
        q.a = road[n]; q.b = road[n+1];
        roadLength += q.len();
    }
    if(uavPlanLength < 1e-6 || roadLength < 1e-6)
        return road[0];

    // find percent along the uavPlan
    int segmentIndex = SnapToSegment(uavPlan,uavLoc,uavPlanLocation);
    double uavPlanDistance = 0.0;
    for(n=0; n<(unsigned int) segmentIndex; n++)
    {
        q.a = uavPlan[n]; q.b = uavPlan[n+1];
        uavPlanDistance += q.len();
    }
    q.a = uavPlan[segmentIndex]; q.b = uavPlan[segmentIndex+1];
    uavPlanDistance += uavPlanLocation.dist(q.a);
    double uavPercentPlan = uavPlanDistance / uavPlanLength;

    // find corresponding road percentage
    double runningDistance = 0.0;
    for(n=0; n<(road.size()-1); n++)
    {
        q.a = road[n]; q.b = road[n+1];
        if( (runningDistance + q.len())/roadLength >= uavPercentPlan )
        {
            if(q.len() < 1e-6)
                return road[n];
            double distanceFromEndpoint = uavPercentPlan*roadLength - runningDistance;
            xyPoint v = q.b - q.a; v = v/q.len();
            xyPoint starePoint = q.a + v*distanceFromEndpoint;
            return starePoint;
        }
        runningDistance += q.len();
    }

    return road[road.size()-1];
}