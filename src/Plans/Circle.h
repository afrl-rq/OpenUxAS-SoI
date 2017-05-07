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
// Circle.h: interface for the CCircle class.
//
//////////////////////////////////////////////////////////////////////

#if !defined(AFX_CIRCLE_H__FDEC0548_7BE2_4C0E_81B0_4B10300842F9__INCLUDED_)
#define AFX_CIRCLE_H__FDEC0548_7BE2_4C0E_81B0_4B10300842F9__INCLUDED_

#if _MSC_VER > 1000
#pragma once
#endif // _MSC_VER > 1000

//#include "GlobalDefines.h"
//#include "TrajectoryDefinitions.h"
#include "Position.h"
#include "Constants/Convert.h"

#include <vector>
namespace n_FrameworkLib
{



    
class CCircle;

    typedef std::vector<CCircle> V_CIRCLE_t;
    typedef V_CIRCLE_t::iterator V_CIRCLE_IT_t;
    typedef V_CIRCLE_t::const_iterator V_CIRCLE_CONST_IT_t;

        
class CCircle : public CPosition
{
public:
    enum enTurnDirection_t 
    {
        turnClockwise=-1,
        turnNone,
        turnCounterclockwise,
        turnNumber
    };    //the +/- 1 and 0 are used in calculations
    
public:
    // default constructor
    CCircle()
        :CPosition(0.0,0.0)
    {
        dGetRadius() = 0.0;
        turnGetTurnDirection() = CCircle::turnNone;
    };
    CCircle(double dCenterX_m,double dCenterY_m,double dRadius_m,enTurnDirection_t turnDirection)
        :CPosition(dCenterX_m,dCenterY_m)
    {
        dGetRadius() = dRadius_m;
        turnGetTurnDirection() = turnDirection;
    };
    CCircle(const CPosition& posCenter,double dRadius_m,enTurnDirection_t turnDirection)
        :CPosition(posCenter)
    {
        dGetRadius() = dRadius_m;
        turnGetTurnDirection() = turnDirection;
    };
    // default destructor
    virtual ~CCircle(){};
    // copy constructer
    CCircle(const CCircle& rhs)
        :CPosition(rhs)
    {
        dGetRadius() = rhs.dGetRadius();
        turnGetTurnDirection() = rhs.turnGetTurnDirection();
    };

    void operator =(const CCircle& rhs)
    {
        CPosition::operator=(rhs);
        dGetRadius() = rhs.dGetRadius();
        turnGetTurnDirection() = rhs.turnGetTurnDirection();
    };

    void operator =(const CPosition& rhs)
    {
        CPosition::operator=(rhs);
    };


public:
    const double& dGetRadius() const {return(m_dRadius_m);};
    double& dGetRadius(){return(m_dRadius_m);};
    void SetRadius(double dRadius_m){m_dRadius_m=n_Const::c_Convert::iRound(dRadius_m);};

    enTurnDirection_t& turnGetTurnDirection(){return(m_turnDirection);};
    const enTurnDirection_t& turnGetTurnDirection()const{return(m_turnDirection);};

    const double dGetAngle(const CPosition& posPoint)const{return(posPoint.relativeAngle2D_rad(*this));};
    const double dGetRelativeAngle(const CPosition& posPoint1,const CPosition& posPoint2)const
    {
        // returns relative angle from point1 to point2 using the circle center as the vertex
        double dAngle1 = posPoint1.relativeAngle2D_rad(*this);
        double dAngle2 = posPoint2.relativeAngle2D_rad(*this);
        if(turnGetTurnDirection() == turnClockwise)
        {
            if(dAngle1 <= dAngle2)
            {
                return((n_Const::c_Convert::dTwoPi() - dAngle2) + dAngle1);
            }
            else
            {
                return(dAngle2 - dAngle1);
            }
        }
        else
        {
            if(dAngle1 <= dAngle2)
            {
                return(dAngle2 - dAngle1);
            }
            else
            {
                return((n_Const::c_Convert::dTwoPi() - dAngle1) + dAngle2);
            }
        }
    };

    void GetNewHeadingAngleAndPosition(double& dFinalHeadingAngle,CPosition& posFinal,double dRotationAngleFinal_rad)const
    {
        // returns a new position and heading of a vehicle on the turn 
        // based on the circle and the final angle (dRotationAngleFinal_rad)
        //
        // the function returns the new heading angle in the reference "dFinalHeadingAngle"
        // and the new position is returned in the "posFinal" reference
        dFinalHeadingAngle = n_Const::c_Convert::dNormalizeAngleRad(dRotationAngleFinal_rad + n_Const::c_Convert::dPiO2());
        posFinal.m_north_m = dGetRadius()*sin(dRotationAngleFinal_rad);
        posFinal.m_east_m = dGetRadius()*cos(dRotationAngleFinal_rad);
    }
    void GetOppositeTurnCircle(double& dFinalHeadingAngle,CCircle& circleOpposite)
    {
        // returns the turn circle that is tangent to this one at the given angle
        circleOpposite.m_north_m = 2.0*dGetRadius()*cos(dFinalHeadingAngle);
        circleOpposite.m_east_m = 2.0*dGetRadius()*sin(dFinalHeadingAngle);
        circleOpposite.SetRadius(dGetRadius());
        circleOpposite.turnGetTurnDirection() = 
                            (turnGetTurnDirection()==turnClockwise)?(turnCounterclockwise):(turnClockwise);
    }
protected:
    //CPosition inherited;
    double m_dRadius_m;
    enTurnDirection_t m_turnDirection;
};

};      //namespace n_FrameworkLib

#endif // !defined(AFX_CIRCLE_H__FDEC0548_7BE2_4C0E_81B0_4B10300842F9__INCLUDED_)
