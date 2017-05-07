// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

//
//    THIS SOFTWARE AND ANY ACCOMPANYING DOCUMENTATION IS RELEASED "AS IS." THE
//    U.S.GOVERNMENT MAKES NO WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, CONCERNING
//    THIS SOFTWARE AND ANY ACCOMPANYING DOCUMENTATION, INCLUDING, WITHOUT LIMITATION,
//    ANY WARRANTIES OF MERCHANTABILITY OR FITNESS FOR A PARTICULAR PURPOSE. IN NO EVENT
//    WILL THE U.S. GOVERNMENT BE LIABLE FOR ANY DAMAGES, INCLUDING ANY LOST PROFITS,
//    LOST SAVINGS OR OTHER INCIDENTAL OR CONSEQUENTIAL DAMAGES ARISING OUT OF THE USE,
//    OR INABILITY TO USE, THIS SOFTWARE OR ANY ACCOMPANYING DOCUMENTATION, EVEN IF
//    INFORMED IN ADVANCE OF THE POSSIBILITY OF SUCH DAMAGES.
//
// HeadingParameters.h: interface for the CHeadingParameters class.
//
//////////////////////////////////////////////////////////////////////

#if !defined(HEADINGPARAMETERS__INCLUDED_)
#define HEADINGPARAMETERS__INCLUDED_

#if _MSC_VER > 1000
#pragma once
#endif // _MSC_VER > 1000

//#include "GlobalDefines.h"

namespace n_FrameworkLib
{

#define DEFAULT_STANDOFF_NO_HEADING_m (50)

class CHeadingParameters
{
public:
    CHeadingParameters(double dHeadingTo_rad=0.0,
        double dStandoff_m=0.0,
        double dFreeToTurn_m=0.0)
        :m_dHeadingTo_rad(dHeadingTo_rad),
        m_dStandoff_m(dStandoff_m),
        m_dFreeToTurn_m(dFreeToTurn_m)
    {};
    ~CHeadingParameters(){};
    CHeadingParameters(const CHeadingParameters& rhs)
    {
        operator =(rhs);
    }
    void operator =(const CHeadingParameters& rhs)
    {
        dGetHeadingTo_rad() = rhs.dGetHeadingTo_rad();
        dGetStandoff_m() = rhs.dGetStandoff_m();
        dGetFreeToTurn_m() = rhs.dGetFreeToTurn_m();
    }
public:
    double& dGetHeadingTo_rad(){return(m_dHeadingTo_rad);};
    const double& dGetHeadingTo_rad()const{return(m_dHeadingTo_rad);};

    double& dGetStandoff_m(){return(m_dStandoff_m);};
    const double& dGetStandoff_m()const{return(m_dStandoff_m);};

    double& dGetFreeToTurn_m(){return(m_dFreeToTurn_m);};
    const double& dGetFreeToTurn_m()const{return(m_dFreeToTurn_m);};

protected:
    double m_dHeadingTo_rad{0.0};
    double m_dStandoff_m{0.0};
    double m_dFreeToTurn_m{0.0};
};

namespace
{
    typedef std::vector<CHeadingParameters> V_HEADING_PARAMETERS_t;
    typedef std::vector<CHeadingParameters>::iterator V_HEADING_PARAMETERS_IT_t;
    typedef std::vector<CHeadingParameters>::const_iterator V_HEADING_PARAMETERS_CONST_IT_t;
}

};      //namespace n_FrameworkLib


#endif // !defined(HEADINGPARAMETERS__INCLUDED_)
