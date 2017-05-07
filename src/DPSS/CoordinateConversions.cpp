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

int Dpss::UavWpToVscsWp(int uavWp)
{
    return uavWp;
}

int Dpss::VscsWpToUavWp(int vscsWp)
{
    return vscsWp;
}

int Dpss::UavWpToStandardWp(int uavWp)
{
    return uavWp;
}

int Dpss::StandardWpToUavWp(int standardWp)
{
    return standardWp;
}

int Dpss::RoadIndexToClosestStandardWp(int roadIndex, int direction)
{
    return roadIndex;
}

int Dpss::StandardWpToRoadIndex(int standardWp)
{
    return standardWp;
}

double Dpss::RoadIndexToNormalizedRoadPos(int roadIndex)
{
    return 0.0;
}

int Dpss::NormalizedRoadPosToClosestRoadIndex(double normalizedRoadPos)
{
    return 0;
}

double Dpss::NormalizedRoadPosToVehiclePos(xyPoint& p, double normalizedRoadPos, int direction)
{
    return 0.0;
}

double Dpss::VehiclePosToNormalizedRoadPos(xyPoint& vehiclePos)
{
    return 0.0;
}

void Dpss::RoadIndexToVehiclePos(xyPoint& p, int roadIndex, int direction)
{
}

int Dpss::VehiclePosToRoadIndex(xyPoint& vehiclePos)
{
    return 0;
}

unsigned short Dpss::NormalizedRoadPosToVscsWp(double roadPos, int direction)
{
    int k, rdA = -1, rdB = -1;
    for(k=0; k<(int)m_TrueRoadLengths.size(); k++)
    {
        if(roadPos < m_TrueRoadLengths[k])
        {
            rdA = k-1;
            rdB = k;
            break;
        }
    }
    if(rdB == 0)
    {
        rdA = 0;
        rdB = 1;
    }
    if(rdB == -1)
    {
        rdB = (int) m_TrueRoadLengths.size() - 1;
        rdA = rdB - 1;
    }

    int trueWp = -1;

    // reminder: road index = m_RdIDList[ waypoint index ]
    if(direction > 0)
    {
        // map to forward direction
        for(k=1; k<m_ReturnPlanWpIndex; k++)
        {
            if(m_RdIDList[k-1] <= rdA && m_RdIDList[k] >= rdB)
            {
                trueWp = k;
                break;
            }
        }
    }
    else
    {
        // map to reverse direction
        for(k=m_ReturnPlanWpIndex+1; k<(int)m_RdIDList.size(); k++)
        {
            if(m_RdIDList[k-1] >= rdB && m_RdIDList[k] <= rdA)
            {
                trueWp = k;
                break;
            }
        }
    }

    if(trueWp >= 0 && trueWp < (int)m_WpIDList.size())
        return ( (unsigned int) (m_WpIDList[trueWp]) );
    if(m_WpIDList.empty())
        return 1;
    return ( ( (unsigned int) m_WpIDList[0]) );
}

void Dpss::RoadPosToWpSegments(xyPoint roadPt, xyPoint& forwardPt, xyPoint& reversePt, int& forwardIndexA, int& forwardIndexB, int& reverseIndexA, int& reverseIndexB)
{
    // set return values to error values
    forwardIndexA = -1;
    forwardIndexB = -1;
    forwardPt = roadPt;

    reverseIndexA = -1;
    reverseIndexB = -1;
    reversePt = roadPt;

    // check for sane road size
    if(m_TrueRoad.empty() || m_TrueRoad.size() < 2)
        return;

    int k, rdA = -1, rdB = -1;
    double dist, minDist = -1.0;

    // find corresponding road segment
    for(k=1; k<(int)m_TrueRoad.size(); k++)
    {
        Segment s;
        s.a = m_TrueRoad[k-1];
        s.b = m_TrueRoad[k];
        dist = s.distToClosestPoint(roadPt);
        if(dist < minDist || minDist < -1e-6)
        {
            rdA = k-1;
            rdB = k;
            minDist = dist;
        }
    }

    int wpA, wpB, trueWp = -1;
    int len = (int)m_WpIDList.size();

    // reminder: road index = m_RdIDList[ waypoint index ]

    // map to forward direction
    for(k=1; k<m_ReturnPlanWpIndex; k++)
    {
        if(m_RdIDList[k-1] <= rdA && m_RdIDList[k] >= rdB)
        {
            trueWp = k;
            break;
        }
    }
    if(trueWp >= 0 && trueWp < len)
    {
        wpA = (trueWp == 0)?(len-1):(trueWp-1);
        wpB = trueWp;
        forwardIndexB = m_WpIDList[wpB];
        forwardIndexA = m_WpIDList[wpA];

        // calculate percentage of road to map to percentage of waypoint segment
        double correspondingRoadLength = 0.0;
        for(k=m_RdIDList[wpA]; k<m_RdIDList[wpB]; k++)
        {
            Segment s(m_TrueRoad[k],m_TrueRoad[k+1]);
            correspondingRoadLength += s.len();
        }

        double percentAlongRoad = 0.0;
        for(k=m_RdIDList[wpA]; k<rdA; k++)
        {
            Segment s(m_TrueRoad[k], m_TrueRoad[k+1]);
            percentAlongRoad += s.len();
        }

        Segment s(m_TrueRoad[rdA], m_TrueRoad[rdB]);
        xyPoint p = s.closestPoint(roadPt);
        p -= s.a;

        percentAlongRoad += p.len();

        if(correspondingRoadLength > 1e-6)
            percentAlongRoad /= correspondingRoadLength;
        else
            percentAlongRoad = 0.0;

        forwardPt = m_TrueWaypoints[wpA]*(1.0 - percentAlongRoad) + m_TrueWaypoints[wpB]*percentAlongRoad;
        
    }
    

    // map to reverse direction
    trueWp = -1;
    for(k=m_ReturnPlanWpIndex+1; k<(int)m_RdIDList.size(); k++)
    {
        if(m_RdIDList[k-1] >= rdB && m_RdIDList[k] <= rdA)
        {
            trueWp = k;
            break;
        }
    }
    if(trueWp >= 0 && trueWp < len)
    {
        wpA = (trueWp == 0)?(len-1):(trueWp-1);
        wpB = trueWp;
        reverseIndexB = m_WpIDList[wpB];
        reverseIndexA = m_WpIDList[wpA];

        // calculate percentage of road to map to percentage of waypoint segment
        double correspondingRoadLength = 0.0;
        for(k=m_RdIDList[wpA]; k>m_RdIDList[wpB]; k--)
        {
            Segment s(m_TrueRoad[k],m_TrueRoad[k-1]);
            correspondingRoadLength += s.len();
        }

        double percentAlongRoad = 0.0;
        for(k=m_RdIDList[wpA]; k>rdB; k--)
        {
            Segment s(m_TrueRoad[k], m_TrueRoad[k-1]);
            percentAlongRoad += s.len();
        }

        Segment s(m_TrueRoad[rdB], m_TrueRoad[rdA]);
        xyPoint p = s.closestPoint(roadPt);
        p -= s.a;

        percentAlongRoad += p.len();

        if(correspondingRoadLength > 1e-6)
            percentAlongRoad /= correspondingRoadLength;
        else
            percentAlongRoad = 0.0;

        reversePt = m_TrueWaypoints[wpA]*(1.0 - percentAlongRoad) + m_TrueWaypoints[wpB]*percentAlongRoad;

    }

}

int Dpss::NormalizedRoadPosToXyRoadPos(xyPoint& p, double x)
{
    int len = (int)m_TrueRoadLengths.size();
    if(x <= 0.0)
    {
        p = m_TrueRoad[0];
        return 1;
    }

    if(x >= 1.0)
    {
        p = m_TrueRoad[len-1];
        return (len-1);
    }

    int upperIndex = 0;
    for(int n=1; n<len; n++)
    {
        if(m_TrueRoadLengths[n] >= x)
        {
            upperIndex = n;
            break;
        }
    }
    if(upperIndex == len)
        upperIndex = len-1;

    Segment rdSegment(m_TrueRoad[upperIndex-1],m_TrueRoad[upperIndex]);
    if( (m_TrueRoadLengths[upperIndex] - m_TrueRoadLengths[upperIndex-1]) > 1e-6 )
    {
        double percentAlong = (x - m_TrueRoadLengths[upperIndex-1])/(m_TrueRoadLengths[upperIndex] - m_TrueRoadLengths[upperIndex-1]);
        p = rdSegment.a + (rdSegment.b - rdSegment.a)*percentAlong;
    }
    else
        p = rdSegment.a;

    return upperIndex;
}

double Dpss::CorrespondingNormalizedRoadLocation(VehicleTelemetry &pos)
{
    int k;
    int toWp;
    int len = (int) m_TrueWaypoints.size();

    xyPoint p;
    Segment q;

    toWp = CurrentSegmentAndXYPosition(pos,p,q);
    if(toWp < 0)
        return -1;

    double bestDist = q.distToClosestPoint(p);
    if(bestDist > m_NearWpThreshold) // || bestDist > q.len()*3)
    {
        // need to search for first segment that meets threshold
        int toReverse = (toWp==0)?(len-1):(toWp-1);
        int toForward = (toWp==(len-1))?(0):(toWp+1);
        int segmentsToCheck = 0;
        while(segmentsToCheck < len)
        {
            // march through plan in reverse and forward directions
            q.a = m_TrueWaypoints[toReverse];
            q.b = m_TrueWaypoints[(toReverse==0)?(len-1):(toReverse-1)];
            if(q.distToClosestPoint(p) < m_NearWpThreshold) // && q.distToClosestPoint(p) < q.len()*3)
            {
                toWp = toReverse;
                bestDist = q.distToClosestPoint(p);
                break;
            }
            if(q.distToClosestPoint(p) < bestDist)
            {
                toWp = toReverse;
                bestDist = q.distToClosestPoint(p);
            }

            segmentsToCheck++;
            if(segmentsToCheck == len) break;
            toReverse--;
            if(toReverse < 0) toReverse = len-1;

            // check forward segment
            q.a = m_TrueWaypoints[toForward];
            q.b = m_TrueWaypoints[(toForward==0)?(len-1):(toForward-1)];
            if(q.distToClosestPoint(p) < m_NearWpThreshold) // && q.distToClosestPoint(p) < q.len()*3)
            {
                toWp = toForward;
                bestDist = q.distToClosestPoint(p);
                break;
            }
            if(q.distToClosestPoint(p) < bestDist)
            {
                toWp = toForward;
                bestDist = q.distToClosestPoint(p);
            }

            segmentsToCheck++;
            toForward++;
            if(toForward >= len) toForward = 0;
        }
    }

    // if on turn-around segment, map to road end point
    if(toWp == m_ReturnPlanWpIndex)
        return 1.0;
    
    // if on turn-around segment, map to road end point
    if(toWp == 0)
        return 0.0;

    // map from waypoint segment to stare points along road
    int frmRdIdx = m_RdIDList[toWp-1]; // should be valid, checked for toWp == 0 above
    int toRdIdx = m_RdIDList[toWp];

    // find distance along calculated best waypoint segment
    Segment s(m_TrueWaypoints[toWp-1],m_TrueWaypoints[toWp]);
    xyPoint projection = s.closestPoint(p);
    projection -= s.a;
    double percentWpTraveled = 0.0;
    if(s.len() > 1e-10)
        percentWpTraveled = projection.len()/s.len();

    double correspondingRoadLength = 0.0;
    xyPoint v;
    if(frmRdIdx == toRdIdx)
        return m_TrueRoadLengths[frmRdIdx];

    if(frmRdIdx > toRdIdx)
    {
        for(k=toRdIdx; k<frmRdIdx; k++)
        {
            v = m_TrueRoad[k+1] - m_TrueRoad[k];
            correspondingRoadLength += v.len(); 
        }
    }
    else
    {
        for(k=frmRdIdx; k<toRdIdx; k++)
        {
            v = m_TrueRoad[k+1] - m_TrueRoad[k];
            correspondingRoadLength += v.len();
        }
    }

    double roadCovered = percentWpTraveled*correspondingRoadLength;
    
    // distance from waypoint to proportional amount of road covered - straight line segments
    Segment rdSegment;
    if(frmRdIdx > toRdIdx)
    {
        for(k=frmRdIdx; k > toRdIdx; k--)
        {
            // get current road segment data
            rdSegment.a = m_TrueRoad[k];
            rdSegment.b = m_TrueRoad[k-1];
            if( roadCovered > rdSegment.len() ) 
                roadCovered -= rdSegment.len();
            else
            {
                if(rdSegment.len() > 1e-6)
                    return m_TrueRoadLengths[k] - roadCovered/rdSegment.len()*(m_TrueRoadLengths[k] - m_TrueRoadLengths[k-1]);
                return m_TrueRoadLengths[k];
            }
        }
    }
    else
    {
        for(k=frmRdIdx; k<toRdIdx; k++)
        {
            // get current road segment data
            rdSegment.a = m_TrueRoad[k];
            rdSegment.b = m_TrueRoad[k+1];
            if (roadCovered > rdSegment.len()) 
                roadCovered -= rdSegment.len();
            else
            {
                if(rdSegment.len() > 1e-6)
                    return ( m_TrueRoadLengths[k] + roadCovered/rdSegment.len()*(m_TrueRoadLengths[k+1] - m_TrueRoadLengths[k]) );
                return m_TrueRoadLengths[k];
            }
        }
    }

    // shouldn't get here: we ran out of length
    return m_TrueRoadLengths[toRdIdx];
}

double Dpss::CorrespondingNormalizedRoadLocation(xyPoint &pos)
{
    int k;
    int toWp;
    int len = (int) m_TrueWaypoints.size();

    if(len < 2) return 0.0;

    xyPoint p = pos;

    // force global search
    Segment q(m_TrueWaypoints[0],m_TrueWaypoints[1]);
    double bestDist = q.distToClosestPoint(p);
    toWp = 1;

    for(k=2; k<len; k++)
    {
        q.a = m_TrueWaypoints[k];
        q.b = m_TrueWaypoints[k-1];
        if(q.distToClosestPoint(p) < bestDist)
        {
            toWp = k;
            bestDist = q.distToClosestPoint(p);
        }
    }

    if(!m_SingleDirectionPlan)
    {
        // check return segment
        q.a = m_TrueWaypoints[len-1];
        q.b = m_TrueWaypoints[0];
        if(q.distToClosestPoint(p) < bestDist)
            toWp = 0;
    }

    // if on turn-around segment, map to road end point
    if(toWp == m_ReturnPlanWpIndex)
        return 1.0;
    
    // if on turn-around segment, map to road end point
    if(toWp == 0)
        return 0.0;

    // map from waypoint segment to stare points along road
    int frmRdIdx = m_RdIDList[toWp-1]; // should be valid, checked for toWp == 0 above
    int toRdIdx = m_RdIDList[toWp];

    // find distance along calculated best waypoint segment
    Segment s(m_TrueWaypoints[toWp-1],m_TrueWaypoints[toWp]);
    xyPoint projection = s.closestPoint(p);
    projection -= s.a;
    double percentWpTraveled = 0.0;
    if(s.len() > 1e-10)
        percentWpTraveled = projection.len()/s.len();

    double correspondingRoadLength = 0.0;
    xyPoint v;
    if(frmRdIdx == toRdIdx)
        return m_TrueRoadLengths[frmRdIdx];

    if(frmRdIdx > toRdIdx)
    {
        for(k=toRdIdx; k<frmRdIdx; k++)
        {
            v = m_TrueRoad[k+1] - m_TrueRoad[k];
            correspondingRoadLength += v.len(); 
        }
    }
    else
    {
        for(k=frmRdIdx; k<toRdIdx; k++)
        {
            v = m_TrueRoad[k+1] - m_TrueRoad[k];
            correspondingRoadLength += v.len();
        }
    }

    double roadCovered = percentWpTraveled*correspondingRoadLength;
    
    // distance from waypoint to proportional amount of road covered - straight line segments
    Segment rdSegment;
    if(frmRdIdx > toRdIdx)
    {
        for(k=frmRdIdx; k > toRdIdx; k--)
        {
            // get current road segment data
            rdSegment.a = m_TrueRoad[k];
            rdSegment.b = m_TrueRoad[k-1];
            if( roadCovered > rdSegment.len() ) 
                roadCovered -= rdSegment.len();
            else
            {
                if(rdSegment.len() > 1e-6)
                    return m_TrueRoadLengths[k] - roadCovered/rdSegment.len()*(m_TrueRoadLengths[k] - m_TrueRoadLengths[k-1]);
                return m_TrueRoadLengths[k];
            }
        }
    }
    else
    {
        for(k=frmRdIdx; k<toRdIdx; k++)
        {
            // get current road segment data
            rdSegment.a = m_TrueRoad[k];
            rdSegment.b = m_TrueRoad[k+1];
            if (roadCovered > rdSegment.len()) 
                roadCovered -= rdSegment.len();
            else
            {
                if(rdSegment.len() > 1e-6)
                    return ( m_TrueRoadLengths[k] + roadCovered/rdSegment.len()*(m_TrueRoadLengths[k+1] - m_TrueRoadLengths[k]) );
                return m_TrueRoadLengths[k];
            }
        }
    }

    // shouldn't get here: we ran out of length
    return m_TrueRoadLengths[toRdIdx];
}