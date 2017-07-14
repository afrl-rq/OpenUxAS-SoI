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
// BaseObject.h: interface for the CBaseObject class.
//
//////////////////////////////////////////////////////////////////////

#if !defined(AFX_BASEOBJECT_H__F3B5500F_0216_47FC_ABF5_E229C9660AD2__INCLUDED_)
#define AFX_BASEOBJECT_H__F3B5500F_0216_47FC_ABF5_E229C9660AD2__INCLUDED_

#if _MSC_VER > 1000
#pragma once
#endif // _MSC_VER > 1000

#include "Position.h"
#include <string>
#include <fstream>

namespace n_FrameworkLib
{
    

class CBaseObject : public CPosition  
{
public:
    CBaseObject()
        :m_iID(-1),
        m_dPsi_rad(0.0),
        m_bValidStartHeading(true)
    {};
    CBaseObject(const int& iID,
                const double& dPositionX,
                const double& dPositionY,
                const double& dPositionZ,
                const double& Psi_rad)
        :CPosition(dPositionX,dPositionY,dPositionZ),
		m_iID(iID),
        m_dPsi_rad(Psi_rad)
    {};
    CBaseObject(const int& iID)
        :m_iID(iID)
    {};
    virtual ~CBaseObject(){};

    CBaseObject(const CBaseObject& rhs)
        : CPosition(rhs)
    {
        SetID(rhs.iGetID());
        SetHeading(rhs.dGetHeading());
        bGetValidStartHeading() = rhs.bGetValidStartHeading();
    };
    void operator=(const CBaseObject& rhs)
    {
        CPosition::operator =(rhs);
        SetID(rhs.iGetID());
        SetHeading(rhs.dGetHeading());
        bGetValidStartHeading() = rhs.bGetValidStartHeading();
    };
public:
    int64_t& iGetID(){return(m_iID);};
    const int64_t& iGetID()const{return(m_iID);};
    void SetID(int64_t iID){m_iID=iID;};

    double& dGetHeading(){return(m_dPsi_rad);};
    const double& dGetHeading() const {return(m_dPsi_rad);};
    void SetHeading(const double dPsi_rad){m_dPsi_rad=dPsi_rad;};

    bool& bGetValidStartHeading(){return(m_bValidStartHeading);};
    const bool& bGetValidStartHeading()const{return(m_bValidStartHeading);};

    int64_t m_iID{-1};
    double m_dPsi_rad{0.0};
    bool m_bValidStartHeading{true};
};


};      //namespace n_FrameworkLib

    

#endif // !defined(AFX_BASEOBJECT_H__F3B5500F_0216_47FC_ABF5_E229C9660AD2__INCLUDED_)
