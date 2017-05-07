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
// PathInformation.h: interface for the CPathInformation class.
//
//
//
//
//////////////////////////////////////////////////////////////////////


#pragma once

#include "Position.h"

#include <map>
#include <memory>       //std::shared_ptr

namespace n_FrameworkLib
{



    class CPathInformation; // need a forward to define typedefs

    typedef std::map<int, CPathInformation> M_INT_PATHINFORMATION_t;
    typedef std::map<int, CPathInformation>::iterator M_INT_PATHINFORMATION_IT_t;
    typedef std::map<int, CPathInformation>::const_iterator M_INT_PATHINFORMATION_CONST_IT_t;
    typedef std::shared_ptr<M_INT_PATHINFORMATION_t> PTR_M_INT_PATHINFORMATION_t;

    typedef std::map<int, PTR_M_INT_PATHINFORMATION_t> M_INT_PTR_M_INT_PATHINFORMATION_t;
    typedef std::map<int, PTR_M_INT_PATHINFORMATION_t>::iterator M_INT_PTR_M_INT_PATHINFORMATION_IT_t;
    typedef std::map<int, PTR_M_INT_PATHINFORMATION_t>::const_iterator M_INT_PTR_M_INT_PATHINFORMATION_CONST_IT_t;
    typedef std::shared_ptr<M_INT_PTR_M_INT_PATHINFORMATION_t> PTR_M_INT_PTR_M_INT_PATHINFORMATION_t;

    class CPathInformation
    {
        //indicies do not include verticies for the begin (vehicle/Objective position) and end (Objective position)
        // length is for full path

    public:

        enum enPathType
        {
            ptypeFlyOverWaypoint,
            ptypeShortestPath,
            ptypeEqualLength,
            ptypeNumber
        };

    public:

        CPathInformation(int iIndexBaseBegin = -1, int iIndexBaseEnd = -1, int iLength = -1)
        : m_iIndexBaseBegin(iIndexBaseBegin),
        m_iIndexBaseEnd(iIndexBaseEnd),
        m_iLength(iLength) { };

        CPathInformation(const CPathInformation& rhs) {
            iGetIndexBaseBegin() = rhs.iGetIndexBaseBegin();
            iGetIndexBaseEnd() = rhs.iGetIndexBaseEnd();
            iGetLength() = rhs.iGetLength();
            posGetStart() = rhs.posGetStart();
            posGetEnd() = rhs.posGetEnd();
        };

        void operator=(const CPathInformation& rhs) {
            iGetIndexBaseBegin() = rhs.iGetIndexBaseBegin();
            iGetIndexBaseEnd() = rhs.iGetIndexBaseEnd();
            iGetLength() = rhs.iGetLength();
            posGetStart() = rhs.posGetStart();
            posGetEnd() = rhs.posGetEnd();
        };
    public:

        int& iGetIndexBaseBegin() {
            return (m_iIndexBaseBegin);
        };

        const int& iGetIndexBaseBegin()const {
            return (m_iIndexBaseBegin);
        };

        int& iGetIndexBaseEnd() {
            return (m_iIndexBaseEnd);
        };

        const int& iGetIndexBaseEnd()const {
            return (m_iIndexBaseEnd);
        };

        int& iGetLength() {
            return (m_iLength);
        };

        const int& iGetLength()const {
            return (m_iLength);
        };

        CPosition& posGetStart() {
            return (m_posStart);
        };

        const CPosition& posGetStart()const {
            return (m_posStart);
        };

        CPosition& posGetEnd() {
            return (m_posEnd);
        };

        const CPosition& posGetEnd()const {
            return (m_posEnd);
        };

    protected:
        int m_iIndexBaseBegin;
        int m_iIndexBaseEnd;
        int m_iLength;
        CPosition m_posStart;
        CPosition m_posEnd;
    };



}; //namespace n_FrameworkLib


