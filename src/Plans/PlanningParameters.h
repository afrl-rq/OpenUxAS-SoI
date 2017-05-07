// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   PlanningParameters.h
 * Author: steve
 *
 * Created on August 22, 2014, 11:03 AM
 */

#ifndef PLANNING_PARAMETERS_H
#define    PLANNING_PARAMETERS_H

#include "Position.h"
#include "TrajectoryParameters.h"
#include "HeadingParameters.h"

#include <vector>

namespace n_FrameworkLib
{

struct PlanningParameters
{
    CPosition positionBegin;
    double m_headingBegin_rad{0.0};
    bool m_isStartHeadingValid{true};
    
    CPosition positionEnd;
    std::vector<CHeadingParameters> headingsToEndPoint;
    double m_StandOffNoHeadings{DEFAULT_STANDOFF_NO_HEADING_m};
    
    double m_waypointSeparationMin_m{0.0};
    double m_turnRadius_m{0.0};

    CTrajectoryParameters::enPathType_t m_pathType{CTrajectoryParameters::pathTurnStraightTurn};
    
    double m_speed_mps{0.0};
    bool m_isFirstObjective{true};
    
    //placeholder
    size_t timePrerequsite_s{0};
    
};

};      //namespace n_FrameworkLib




#endif    /* PLANNING_PARAMETERS_H */

