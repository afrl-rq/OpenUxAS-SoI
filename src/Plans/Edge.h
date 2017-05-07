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
// Edge.h: interface for the CEdge class.
//
//
//
//////////////////////////////////////////////////////////////////////

#if !defined(AFX_EDGE_H__CE91A42E_2AFF_46F1_9D41_15AD11E2A6D6__INCLUDED_)
#define AFX_EDGE_H__CE91A42E_2AFF_46F1_9D41_15AD11E2A6D6__INCLUDED_

#if _MSC_VER > 1000
#pragma once
#endif // _MSC_VER > 1000

//#include "GlobalDefines.h"
#include "Position.h"
#include "Constants/Constants_Control.h"

#include <cstdint>
#include <list>

namespace n_FrameworkLib
{

extern CPosition cnst_posDefault; 
class CEdge
{
public:    //typedefs

    //edge vector
    typedef std::vector<CEdge> V_EDGE_t;
    typedef std::vector<CEdge>::iterator V_EDGE_IT_t;
    typedef std::vector<CEdge>::const_iterator V_EDGE_CONST_IT_t;
    //edge list
    typedef std::list<CEdge> L_EDGE_t;
    typedef std::list<CEdge>::iterator L_EDGE_IT_t;
    typedef std::list<CEdge>::const_iterator L_EDGE_CONST_IT_t;

    using first_type = n_Const::PlanCost_t;    //for boost    
    using second_type = n_Const::PlanCost_t;    //for boost

public:    //enumerations
public:    //constructors/destructors
    CEdge(n_Const::PlanCost_t iVertex1=-1,n_Const::PlanCost_t iVertex2=-1,n_Const::PlanCost_t iLength=0)
        :first(iVertex1),second(iVertex2),m_iLength(iLength)
    {};

    CEdge(const CEdge& rhs)
    {
        first = rhs.first;
        second = rhs.second;
        iGetLength() = rhs.iGetLength();
    };

    void operator =(const CEdge& rhs)
    {
        first = rhs.first;
        second = rhs.second;
        iGetLength() = rhs.iGetLength();
    };

    bool operator ==(const CEdge& rhs)
    {
        return((first == rhs.first)&&(second == rhs.second));
    };

public:    //methods/functions
    bool bFindIntersection(const CPosition& posPointA1, const CPosition& posPointA2, const CPosition& posPointB1, const CPosition& posPointB2, CPosition& posIntersectionPoint = cnst_posDefault);
    bool bIntersection(const V_POSITION_t& cVertexContainer, const CPosition& posThatB1, const CPosition& posThatB2,const n_Const::PlanCost_t& i32IndexA=-1,const n_Const::PlanCost_t& i32IndexB=-1,CPosition& posIntersectionPoint=cnst_posDefault);
    bool bIntersection(const V_POSITION_t& cVertexContainer,const CEdge& eThat,CPosition& posIntersectionPoint=cnst_posDefault);
    bool bIntersection(const V_POSITON_ID_t& cVertexContainer,const CEdge& eThat,CPosition& posIntersectionPoint=cnst_posDefault);

public:    //accessors

    n_Const::PlanCost_t& iGetLength(){return(m_iLength);};
    const n_Const::PlanCost_t& iGetLength()const{return(m_iLength);};

    //the definition of first and second lets the CEdge class work with the boost graph libray
    first_type first;
    second_type second;

protected:    //storage
    n_Const::PlanCost_t m_iLength;
};


std::ostream &operator << (std::ostream &os,const CEdge& edgeRhs);

}       //namespace n_FrameworkLib

#endif // !defined(AFX_EDGE_H__CE91A42E_2AFF_46F1_9D41_15AD11E2A6D6__INCLUDED_)
