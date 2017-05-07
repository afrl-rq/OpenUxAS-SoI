// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#pragma once
#include "DpssDataTypes.h"
#include <vector>

class SegmentMap
{
public:
    SegmentMap();
    SegmentMap(std::vector<xyPoint>& uavPlan, std::vector<xyPoint>& road);
    ~SegmentMap();

    void Initialize(std::vector<xyPoint>& uavPlan, std::vector<xyPoint>& road);
    xyPoint CalculateStarePoint(xyPoint& uavLoc);
    static xyPoint CalculateStarePoint(std::vector<xyPoint>& uavPlan, std::vector<xyPoint>& road, xyPoint& uavLoc);
    static int SnapToSegment(std::vector<xyPoint>& polyline, xyPoint& actualLocation, xyPoint& snappedLocation);

private:
    std::vector<xyPoint> path;
    std::vector<xyPoint> plan;
    std::vector<double> normalizedPathLengths;
    double totalPlanLength;
    double totalPathLength;
};