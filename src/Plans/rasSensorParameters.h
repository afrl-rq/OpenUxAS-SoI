// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

//
// rasSensorParameters.h: interface for the rasCSensorParameters class.
//
//////////////////////////////////////////////////////////////////////

#pragma once


//#include "GlobalDefines.h"

namespace RAS080808
{


class rasCSensorParameters
{
public:    //enumerations
public:
    rasCSensorParameters():
            m_iID(-1),
            m_snsrtypSensorType(imgtypUnknown),
            m_reSensorFieldOfViewHorizantalNominal_rad(n_reSensorFieldOfViewHorizantal_rad),
            m_reSensorFieldOfViewHorizantalMax_rad(n_reSensorFieldOfViewHorizantal_rad),
            m_reSensorFieldOfViewHorizantalMin_rad(n_reSensorFieldOfViewHorizantal_rad),
            m_reSensorFieldOfViewVerticalNominal_rad(n_reSensorFieldOfViewVertical_rad),
            m_reSensorFieldOfViewVerticalMax_rad(n_reSensorFieldOfViewVertical_rad),
            m_reSensorFieldOfViewVerticalMin_rad(n_reSensorFieldOfViewVertical_rad),
            m_rePixelSpacing_m(-1.0),
            m_reSensorRelativeHeadingNominal_rad(n_reSensorRelativeHeading_rad),
            m_reSensorRelativeHeadingMax_rad(0.0),
            m_reSensorRelativeHeadingMin_rad(0.0),
            m_reSensorDepressionAngleNominal_rad(n_reSensorDepressionAngle_rad),
            m_reSensorDepressionAngleMax_rad(0.0),
            m_reSensorDepressionAngleMin_rad(0.0)
            {};

    virtual ~rasCSensorParameters(){};

    // copy constructer
    rasCSensorParameters(const rasCSensorParameters& rhs)
    {
        //sensor parameters
        iGetID() = rhs.iGetID();
        snsrtypGetSensorType() = rhs.snsrtypGetSensorType();

        reGetSensorFieldOfViewHorizantalNominal_rad() = rhs.reGetSensorFieldOfViewHorizantalNominal_rad();
        reGetSensorFieldOfViewHorizantalMax_rad() = rhs.reGetSensorFieldOfViewHorizantalMax_rad();
        reGetSensorFieldOfViewHorizantalMin_rad() = rhs.reGetSensorFieldOfViewHorizantalMin_rad();

        reGetSensorFieldOfViewVerticalNominal_rad() = rhs.reGetSensorFieldOfViewVerticalNominal_rad();
        reGetSensorFieldOfViewVerticalMax_rad() = rhs.reGetSensorFieldOfViewVerticalMax_rad();
        reGetSensorFieldOfViewVerticalMin_rad() = rhs.reGetSensorFieldOfViewVerticalMin_rad();

        reGetPixelSpacing_m() = rhs.reGetPixelSpacing_m();

        reGetSensorRelativeHeadingNominal_rad() = rhs.reGetSensorRelativeHeadingNominal_rad();
        reGetSensorRelativeHeadingMax_rad() = rhs.reGetSensorRelativeHeadingMax_rad();
        reGetSensorRelativeHeadingMin_rad() = rhs.reGetSensorRelativeHeadingMin_rad();
        reGetSensorDepressionAngleNominal_rad() = rhs.reGetSensorDepressionAngleNominal_rad();
        reGetSensorDepressionAngleMax_rad() = rhs.reGetSensorDepressionAngleMax_rad();
        reGetSensorDepressionAngleMin_rad() = rhs.reGetSensorDepressionAngleMin_rad();
    };

    // operator =
    void operator=(const rasCSensorParameters& rhs)
    {
        iGetID() = rhs.iGetID();
        snsrtypGetSensorType() = rhs.snsrtypGetSensorType();

        reGetSensorFieldOfViewHorizantalNominal_rad() = rhs.reGetSensorFieldOfViewHorizantalNominal_rad();
        reGetSensorFieldOfViewHorizantalMax_rad() = rhs.reGetSensorFieldOfViewHorizantalMax_rad();
        reGetSensorFieldOfViewHorizantalMin_rad() = rhs.reGetSensorFieldOfViewHorizantalMin_rad();

        reGetSensorFieldOfViewVerticalNominal_rad() = rhs.reGetSensorFieldOfViewVerticalNominal_rad();
        reGetSensorFieldOfViewVerticalMax_rad() = rhs.reGetSensorFieldOfViewVerticalMax_rad();
        reGetSensorFieldOfViewVerticalMin_rad() = rhs.reGetSensorFieldOfViewVerticalMin_rad();

        reGetPixelSpacing_m() = rhs.reGetPixelSpacing_m();

        reGetSensorRelativeHeadingNominal_rad() = rhs.reGetSensorRelativeHeadingNominal_rad();
        reGetSensorRelativeHeadingMax_rad() = rhs.reGetSensorRelativeHeadingMax_rad();
        reGetSensorRelativeHeadingMin_rad() = rhs.reGetSensorRelativeHeadingMin_rad();
        reGetSensorDepressionAngleNominal_rad() = rhs.reGetSensorDepressionAngleNominal_rad();
        reGetSensorDepressionAngleMax_rad() = rhs.reGetSensorDepressionAngleMax_rad();
        reGetSensorDepressionAngleMin_rad() = rhs.reGetSensorDepressionAngleMin_rad();
    };


public:    //member functions
    double reGetAltitude_mBasedOnGroundSampleDistance_m(const double& reGroundSampleDistance_m)
    {
        double reAltitude_m(0.0);

        //TODO:: need to add this calculation based on FOV and reGetPixelSpacing_m() and gimble angles
        reAltitude_m = 1000.0;    //use some constant for the time being

        return(reAltitude_m);
    }
    double reGetGroundSampleDistance_mBasedOnAltitude_m(const double& reAltitude_m)
    {
        double reResoluiton_m(0.0);

        //TODO:: need to add this calculation based on FOV and reGetPixelSpacing_m() and gimble angles
        reResoluiton_m = 0.5;    //use some constant for the time being

        return(reResoluiton_m);
    }



    void CalculateSensorFootprintParameters(const double& dAltitude,
                                            double& reDistanceVehicleToCenterOfSensorFootprint_m,
                                            double& reDistanceSensorCenterToLeadingEdge_m,
                                            double& reDistanceSensorTrailingEdgeToCenter_m
                                            )
    {
        double reDenominator = tan(reGetSensorDepressionAngleNominal_rad() - (reGetSensorFieldOfViewVerticalNominal_rad()/2.0));
        double reSensorDistanceMax = (n_Const::c_Convert::bCompareDouble(reDenominator,0.0,n_Const::c_Convert::enEqual))?(0.0):(dAltitude/reDenominator);
        reDenominator = tan(reGetSensorDepressionAngleNominal_rad() + (reGetSensorFieldOfViewVerticalNominal_rad()/2.0));
        double reSensorDistanceMin = (n_Const::c_Convert::bCompareDouble(reDenominator,0.0,n_Const::c_Convert::enEqual))?(0.0):(dAltitude/reDenominator);
        reDenominator = tan(reGetSensorDepressionAngleNominal_rad());
        reDistanceVehicleToCenterOfSensorFootprint_m = (n_Const::c_Convert::bCompareDouble(reDenominator,0.0,n_Const::c_Convert::enEqual))?(0.0):(dAltitude/reDenominator);
        reDistanceSensorCenterToLeadingEdge_m = reSensorDistanceMax - reDistanceVehicleToCenterOfSensorFootprint_m;
        reDistanceSensorTrailingEdgeToCenter_m = reDistanceVehicleToCenterOfSensorFootprint_m - reSensorDistanceMin;
    };

    //double    reSensorWidth = 2.0*(dAltitude*
    //                                tan(reGetSensorFieldOfViewHorizantalNominal_rad()/2.0))/
    //                                (-tan(reGetSensorFieldOfViewVerticalNominal_rad()/2.0)*
    //                                cos(reGetSensorDepressionAngleNominal_rad())+
    //                                sin(reGetSensorDepressionAngleNominal_rad()));

public:    //accessor functions
    int& iGetID(){return(m_iID);};
    const int& iGetID()const{return(m_iID);};

    enSensorType& snsrtypGetSensorType(){return(m_snsrtypSensorType);};
    const enSensorType& snsrtypGetSensorType()const{return(m_snsrtypSensorType);};

    double& reGetSensorFieldOfViewHorizantalNominal_rad(){return(m_reSensorFieldOfViewHorizantalNominal_rad);};
    const double& reGetSensorFieldOfViewHorizantalNominal_rad()const{return(m_reSensorFieldOfViewHorizantalNominal_rad);};

    double& reGetSensorFieldOfViewHorizantalMax_rad(){return(m_reSensorFieldOfViewHorizantalMax_rad);};
    const double& reGetSensorFieldOfViewHorizantalMax_rad()const{return(m_reSensorFieldOfViewHorizantalMax_rad);};

    double& reGetSensorFieldOfViewHorizantalMin_rad(){return(m_reSensorFieldOfViewHorizantalMin_rad);};
    const double& reGetSensorFieldOfViewHorizantalMin_rad()const{return(m_reSensorFieldOfViewHorizantalMin_rad);};

    double& reGetSensorFieldOfViewVerticalNominal_rad(){return(m_reSensorFieldOfViewVerticalNominal_rad);};
    const double& reGetSensorFieldOfViewVerticalNominal_rad()const{return(m_reSensorFieldOfViewVerticalNominal_rad);};

    double& reGetSensorFieldOfViewVerticalMax_rad(){return(m_reSensorFieldOfViewVerticalMax_rad);};
    const double& reGetSensorFieldOfViewVerticalMax_rad()const{return(m_reSensorFieldOfViewVerticalMax_rad);};

    double& reGetSensorFieldOfViewVerticalMin_rad(){return(m_reSensorFieldOfViewVerticalMin_rad);};
    const double& reGetSensorFieldOfViewVerticalMin_rad()const{return(m_reSensorFieldOfViewVerticalMin_rad);};

    double& reGetPixelSpacing_m(){return(m_rePixelSpacing_m);};
    const double& reGetPixelSpacing_m()const{return(m_rePixelSpacing_m);};

    double& reGetSensorRelativeHeadingNominal_rad(){return(m_reSensorRelativeHeadingNominal_rad);};
    const double& reGetSensorRelativeHeadingNominal_rad()const{return(m_reSensorRelativeHeadingNominal_rad);};

    double& reGetSensorRelativeHeadingMax_rad(){return(m_reSensorRelativeHeadingMax_rad);};
    const double& reGetSensorRelativeHeadingMax_rad()const{return(m_reSensorRelativeHeadingMax_rad);};

    double& reGetSensorRelativeHeadingMin_rad(){return(m_reSensorRelativeHeadingMin_rad);};
    const double& reGetSensorRelativeHeadingMin_rad()const{return(m_reSensorRelativeHeadingMin_rad);};

    double& reGetSensorDepressionAngleNominal_rad(){return(m_reSensorDepressionAngleNominal_rad);};
    const double& reGetSensorDepressionAngleNominal_rad()const{return(m_reSensorDepressionAngleNominal_rad);};

    double& reGetSensorDepressionAngleMax_rad(){return(m_reSensorDepressionAngleMax_rad);};
    const double& reGetSensorDepressionAngleMax_rad()const{return(m_reSensorDepressionAngleMax_rad);};

    double& reGetSensorDepressionAngleMin_rad(){return(m_reSensorDepressionAngleMin_rad);};
    const double& reGetSensorDepressionAngleMin_rad()const{return(m_reSensorDepressionAngleMin_rad);};


protected:
    int m_iID;
    enSensorType m_snsrtypSensorType;
    double m_reSensorFieldOfViewHorizantalNominal_rad;
    double m_reSensorFieldOfViewHorizantalMax_rad;
    double m_reSensorFieldOfViewHorizantalMin_rad;

    double m_reSensorFieldOfViewVerticalNominal_rad;
    double m_reSensorFieldOfViewVerticalMax_rad;
    double m_reSensorFieldOfViewVerticalMin_rad;

    double m_rePixelSpacing_m;

    double m_reSensorRelativeHeadingNominal_rad;    //Heading relative to the vehicle, i.e. measured from the xbody axis , i.e. out the nose, clockwize
    double m_reSensorRelativeHeadingMax_rad;
    double m_reSensorRelativeHeadingMin_rad;

    double m_reSensorDepressionAngleNominal_rad;
    double m_reSensorDepressionAngleMax_rad;
    double m_reSensorDepressionAngleMin_rad;
};

typedef vector<rasCSensorParameters> V_SENSORPARAMETERS_t;
typedef vector<rasCSensorParameters>::iterator V_SENSORPARAMETERS_IT_t;
typedef vector<rasCSensorParameters>::const_iterator V_SENSORPARAMETERS_CONST_IT_t;

}    //namespace RAS080808

using namespace RAS080808;

