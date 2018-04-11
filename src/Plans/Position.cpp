// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

// Position.cpp: implementation of the CPosition class.
//
//////////////////////////////////////////////////////////////////////

#include "Position.h"

namespace n_FrameworkLib
{
    


std::ostream&  operator<<(std::basic_ostream<char, std::char_traits<char> >& os, CPosition const& posRhs)
//ostream& operator << (ostream &os,const CPosition& posRhs)
{
#ifdef MATLAB_PLOT
        os << "[" << posRhs.m_north_m << ","
            << posRhs.m_east_m << ","
            << posRhs.m_altitude_m << "]";
#else    //#ifdef MATLAB_PLOT
        os << posRhs.m_north_m << ","
            << posRhs.m_east_m << ","
            << posRhs.m_altitude_m;
#endif    //#ifdef MATLAB_PLOT

        return os;
}


};      //namespace n_FrameworkLib