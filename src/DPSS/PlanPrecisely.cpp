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
using namespace std;

double Dpss::PlanCost(std::vector<double>& x)
{
    std::vector<double> y;
    y.assign(x.begin(), x.end());

    sort(y.begin(),y.end());
    int N = (int) y.size();

    // 0 index
    double cost = MaxDeviation(0.0, y[0]);

    // middle indices
    for(int k=1; k<((int)x.size()); k++)
        cost += MaxDeviation(y[k-1],y[k]);

    // N-1 index
    cost += MaxDeviation(y[N-1],1.0);

    return cost;
}

double Dpss::MaxDeviation(double a, double b)
{
    int A = 0;
    int B = ((int)m_PrecisePlanLengths.size()) - 1;
    int k;

    if(a < 0.0) a = 0.0;
    if(a > 1.0) a = 1.0;
    if(b < 0.0) b = 0.0;
    if(b > 1.0) b = 1.0;
    if(a > b) { double t = a; a = b; b = t; }

    for(k=1; k<(int)m_PrecisePlanLengths.size(); k++)
    {
        if(m_PrecisePlanLengths[k] >= a)
        {
            A = k;
            break;
        }
    }

    for(k=1; k<(int)m_PrecisePlanLengths.size(); k++)
    {
        if(m_PrecisePlanLengths[k] >= b)
        {
            B = k;
            break;
        }
    }

    if(A == B) return 0.0;

    Segment rdSegmentA(m_PrecisePlanRoad[A-1],m_PrecisePlanRoad[A]);
    Segment rdSegmentB(m_PrecisePlanRoad[B-1],m_PrecisePlanRoad[B]);

    Segment wpSegment;
    double percentAlong = 0.0;
    if((m_PrecisePlanLengths[A] - m_PrecisePlanLengths[A-1]) > 1e-6)
        percentAlong = (a - m_PrecisePlanLengths[A-1])/(m_PrecisePlanLengths[A] - m_PrecisePlanLengths[A-1]);
    if(rdSegmentA.len() > 1e-10)
        wpSegment.a = rdSegmentA.a + (rdSegmentA.b - rdSegmentA.a)*(percentAlong/rdSegmentA.len());
    else
        wpSegment.a = rdSegmentA.a;

    percentAlong = 0.0;
    if((m_PrecisePlanLengths[B] - m_PrecisePlanLengths[B-1]) > 1e-6)
        percentAlong = (b - m_PrecisePlanLengths[B-1])/(m_PrecisePlanLengths[B] - m_PrecisePlanLengths[B-1]);
    if(rdSegmentB.len() > 1e-10)
        wpSegment.b = rdSegmentB.a + (rdSegmentB.b - rdSegmentB.a)*(percentAlong/rdSegmentB.len());
    else
        wpSegment.b = rdSegmentB.a;

    
    double deviation = 0.0;
    for(k=A; k<B; k++)
    {
        double instantaneousDeviation = wpSegment.distToClosestPoint(m_PrecisePlanRoad[k]);
        if(instantaneousDeviation > deviation)
            deviation = instantaneousDeviation;
    }

    return 0.5*deviation*wpSegment.len();
}
