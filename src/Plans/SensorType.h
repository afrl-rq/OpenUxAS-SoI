// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

// SensorType.h: interface for the CSensorType class.
//
//////////////////////////////////////////////////////////////////////

#if !defined(AFX_SENSORTYPE_H__EA1EED3B_A6D8_4BBE_8D3F_9B9428122C78__INCLUDED_)
#define AFX_SENSORTYPE_H__EA1EED3B_A6D8_4BBE_8D3F_9B9428122C78__INCLUDED_

#if _MSC_VER > 1000
#pragma once
#endif // _MSC_VER > 1000

#include "GlobalDefinitions.h"


namespace n_FrameworkLib
{

class CSensorType  
{
public:
    CSensorType(REAL_NUMBER_t reDistanceFromVehicleMin_m,
                REAL_NUMBER_t reDistanceFromVehicleMax_m,
                REAL_NUMBER_t reWidth_m,
                REAL_NUMBER_t RelativeHeading_rad
    )
    :m_reDistanceFromVehicleMin_m(reDistanceFromVehicleMin_m),
    m_reDistanceFromVehicleMax_m(reDistanceFromVehicleMax_m),
    m_reWidth_m(reWidth_m),
    m_RelativeHeading_rad(RelativeHeading_rad),
    {};
    virtual ~CSensorType(){};

public:    //accessors
    REAL_NUMBER_t& reGetDistanceFromVehicleMin(){return(m_reDistanceFromVehicleMin_m);};
    const REAL_NUMBER_t& reGetDistanceFromVehicleMin()const{return(m_reDistanceFromVehicleMin_m);};

    REAL_NUMBER_t& reGetDistanceFromVehicleMax(){return(m_reDistanceFromVehicleMax_m);};
    const REAL_NUMBER_t& reGetDistanceFromVehicleMax()const{return(m_reDistanceFromVehicleMax_m);};

    REAL_NUMBER_t& reGetWidth(){return(m_reWidth_m);};
    const REAL_NUMBER_t& reGetWidth()const{return(m_reWidth_m);};

    REAL_NUMBER_t& reGetRelativeHeading(){return(m_reRelativeHeading_rad);};
    const REAL_NUMBER_t& reGetRelativeHeading()const{return(m_reRelativeHeading_rad);};


protected:

    REAL_NUMBER_t m_reDistanceFromVehicleMin_m;
    REAL_NUMBER_t m_reDistanceFromVehicleMax_m;
    REAL_NUMBER_t m_reWidth_m;
    REAL_NUMBER_t m_reRelativeHeading_rad;    //Heading relative to the vehicle, i.e. measured from the xbody axis , i.e. out the nose, clockwize

};

}    //namespace n_FrameworkLib

#endif // !defined(AFX_SENSORTYPE_H__EA1EED3B_A6D8_4BBE_8D3F_9B9428122C78__INCLUDED_)
