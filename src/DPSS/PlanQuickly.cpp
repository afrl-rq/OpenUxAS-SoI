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

void Dpss::PlanQuickly(std::vector<xyPoint>& xyPoints, int maxWps)
{
    vector<double> effect;
    double seperation, beta, leastAffected;
    int i, leastAffectedIndex, len = (int) xyPoints.size();
    vector<xyPoint> accurateRoad(xyPoints);
    
    // starting fresh
    effect.clear();
    m_QuickPlanIndices.clear();

    effect.push_back(0.0);
    m_QuickPlanIndices.push_back(0);
    for(int k=1; k < (len-1); k++)
    {
        seperation = ComputeSeperation(beta, xyPoints[k-1], xyPoints[k], xyPoints[k+1]);
        effect.push_back(seperation);
        m_QuickPlanIndices.push_back(k);
    }
    effect.push_back(0.0);
    m_QuickPlanIndices.push_back(len-1);

    while( (int)xyPoints.size() > maxWps )
    {
        len = (int) effect.size();

        // find initial point that is possible to remove
        leastAffectedIndex = -1;
        for(i=1; i<(len-1); i++)
        {
            if(xyPoints[i].attributes == Dpss_Data_n::xyPoint::None)
            {
                leastAffected = effect[i];
                leastAffectedIndex = i;
                break;
            }
        }

        // check to see if there are any points that can be removed
        // should not get here - requires more than expected waypoints
        if(leastAffectedIndex < 0)
            return;
        
        // find least effected point and remove
        for(i=leastAffectedIndex+1; i<(len-1); i++)
        {
            if(effect[i] < leastAffected && xyPoints[i].attributes == Dpss_Data_n::xyPoint::None)
            {
                leastAffected = effect[i];
                leastAffectedIndex = i;
            }
        }
        
        vector<double>::iterator effectIter = effect.begin() + leastAffectedIndex;
        effectIter = effect.erase(effectIter);
        vector<xyPoint>::iterator pointIter = xyPoints.begin() + leastAffectedIndex;
        pointIter = xyPoints.erase(pointIter);
        vector<int>::iterator origIter = m_QuickPlanIndices.begin() + leastAffectedIndex;
        origIter = m_QuickPlanIndices.erase(origIter);

        // recompute effect for index, index-1
        len = (int) effect.size();
        if(leastAffectedIndex < (len-1) && leastAffectedIndex > 0)
        {
            effect[leastAffectedIndex] = ComputeSeperation(beta, xyPoints[leastAffectedIndex-1], xyPoints[leastAffectedIndex], xyPoints[leastAffectedIndex+1]);
            for( i = (m_QuickPlanIndices[leastAffectedIndex-1]+1); i < m_QuickPlanIndices[leastAffectedIndex+1]; i++ )
            {
                seperation = ComputeSeperation(beta, xyPoints[leastAffectedIndex-1], accurateRoad[i], xyPoints[leastAffectedIndex+1]);
                if(seperation > effect[leastAffectedIndex])
                    effect[leastAffectedIndex] = seperation;
            }
        }
        if(leastAffectedIndex > 1 && leastAffectedIndex < len)
        {
            effect[leastAffectedIndex-1] = ComputeSeperation(beta, xyPoints[leastAffectedIndex-2], xyPoints[leastAffectedIndex-1], xyPoints[leastAffectedIndex]);
            for( i = (m_QuickPlanIndices[leastAffectedIndex-2]+1); i < m_QuickPlanIndices[leastAffectedIndex]; i++ )
            {
                seperation = ComputeSeperation(beta, xyPoints[leastAffectedIndex-2], accurateRoad[i], xyPoints[leastAffectedIndex]);
                if(seperation > effect[leastAffectedIndex-1])
                    effect[leastAffectedIndex-1] = seperation;
            }
        }
    }
}