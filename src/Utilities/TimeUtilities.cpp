// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   TimeUtilities.cpp
 * Author: steve
 * 
 * Created on March 19, 2012, 12:04 PM
 */

#include "TimeUtilities.h"
#include <mutex>


namespace uxas
{
namespace common
{
namespace utilities
{

const std::chrono::microseconds uxas::common::utilities::c_TimeUtilities::_oneHundredMicroseconds = { std::chrono::microseconds(100)};
    
    
const n_POSIX_TIME::ptime uxas::common::utilities::c_TimeUtilities::n_ptimeTime_Jan_01_1970(boost::gregorian::date(1970, boost::gregorian::Jan, 1), n_POSIX_TIME::time_duration(0, 0, 0));
const n_POSIX_TIME::ptime uxas::common::utilities::c_TimeUtilities::n_ptimeTime_Jan_01_2013(boost::gregorian::date(2013, boost::gregorian::Jan, 1), n_POSIX_TIME::time_duration(0, 0, 0));
const n_POSIX_TIME::ptime uxas::common::utilities::c_TimeUtilities::n_ptimeTime_Jan_01_2030(boost::gregorian::date(2030, boost::gregorian::Jan, 1), n_POSIX_TIME::time_duration(0, 0, 0));

n_POSIX_TIME::ptime uxas::common::utilities::c_TimeUtilities::m_ptimeTimeInitial = n_POSIX_TIME::microsec_clock::universal_time();
#ifdef TIME_ADD_INITIAL_CORRECTION_OFFSET
n_POSIX_TIME::time_duration uxas::common::utilities::c_TimeUtilities::m_tmdrtnTimeCorrection = uxas::common::utilities::c_TimeUtilities::n_ptimeTime_Jan_01_2013 - uxas::common::utilities::c_TimeUtilities::n_ptimeTime_Jan_01_1970;
#else   //TIME_ADD_INITIAL_CORRECTION_OFFSET
n_POSIX_TIME::time_duration uxas::common::utilities::c_TimeUtilities::m_tmdrtnTimeCorrection(0, 0, 0, 0);
#endif//TIME_ADD_INITIAL_CORRECTION_OFFSET
bool uxas::common::utilities::c_TimeUtilities::m_bTimeCorrected(false);


uxas::common::utilities::c_TimeUtilities::c_TimeUtilities()
{
    ptimeGetTimeInitial() = n_POSIX_TIME::microsec_clock::universal_time();
};

void uxas::common::utilities::c_TimeUtilities::SetTimeCorrection_tmdrtn(n_POSIX_TIME::time_duration& tmdrtnTimeCorrection)
{
    std::lock_guard<std::mutex> lock(*(reinterpret_cast<std::mutex*>(pmtxGetTimeSyncMutex())));
    m_tmdrtnTimeCorrection = tmdrtnTimeCorrection;
//    if(!bGetTimeCorrected())
//    {
//        ptimeGetTimeInitial() = n_POSIX_TIME::microsec_clock::universal_time();
//    }
    bSetTimeCorrected_b(true);
};

uxas::common::utilities::mutex* uxas::common::utilities::c_TimeUtilities::m_pmtxTimeSyncMutex = reinterpret_cast<uxas::common::utilities::mutex*>(new std::mutex);

    uint32_t uxas::common::utilities::c_TimeUtilities::uiGetTime2030_s()
    {
        n_POSIX_TIME::time_duration ptdDuration = ptimeGetTime_Jan_01_2030() - ptimeGetTime_Jan_01_1970();
        uint32_t  uiTime_s = ptdDuration.total_milliseconds()/1000 + tmdrtnGetTimeCorrection().total_seconds();
 
        return(uiTime_s);
    }
    int64_t uxas::common::utilities::c_TimeUtilities::getTime2030_ms()
    {
        n_POSIX_TIME::time_duration ptdDuration = ptimeGetTime_Jan_01_2030() - ptimeGetTime_Jan_01_1970();
        int64_t  uiTime_s = ptdDuration.total_milliseconds() + tmdrtnGetTimeCorrection().total_milliseconds();
 
        return(uiTime_s);
    }
    
    uint32_t uxas::common::utilities::c_TimeUtilities::uiGetTimeNow_s()
    {
        return(static_cast<uint32_t>(getTimeNow_ms()/1000));
    }
    
    int64_t uxas::common::utilities::c_TimeUtilities::getTimeNow_ms(const bool& bCorrected)
    {
        n_POSIX_TIME::ptime ptimeTimeNow = n_POSIX_TIME::microsec_clock::universal_time();
        n_POSIX_TIME::time_duration ptdDuration = ptimeTimeNow - ptimeGetTime_Jan_01_1970();
        int64_t timeNow_ms = static_cast<int64_t>(ptdDuration.total_milliseconds());
        if(bCorrected)
        {
            timeNow_ms += static_cast<int64_t>(tmdrtnGetTimeCorrection().total_milliseconds());
        }
        return(timeNow_ms);
    }
    
    double uxas::common::utilities::c_TimeUtilities::dGetTimeNow_s(const bool& bCorrected)
    {
        n_POSIX_TIME::ptime ptimeTimeNow = n_POSIX_TIME::microsec_clock::universal_time();
        n_POSIX_TIME::time_duration ptdDuration = ptimeTimeNow - ptimeGetTime_Jan_01_1970();
        
        double dTimeNow_s = static_cast<double>(ptdDuration.total_milliseconds())/1000.0;
        if(bCorrected)
        {
            dTimeNow_s += static_cast<double>(tmdrtnGetTimeCorrection().total_milliseconds())/1000.0;            
        }
        //std::cout << "***### dTimeNow_s[" << static_cast<uint32_t>(dTimeNow_s) << "]" << std::endl;
        
        return(dTimeNow_s);
    }
    
    uint32_t uxas::common::utilities::c_TimeUtilities::uiGetTimeSinceStart_s()
    {
        
        uint32_t  uiTime_s = static_cast<uint32_t>(std::round(dGetTimeSinceStart_s()));
        
        return(uiTime_s);
    }
    
    double uxas::common::utilities::c_TimeUtilities::dGetTimeSinceStart_s()
    {
        n_POSIX_TIME::ptime ptimeTimeNow = n_POSIX_TIME::microsec_clock::universal_time();
        n_POSIX_TIME::time_duration ptdDuration = ptimeTimeNow - ptimeGetTimeInitial();
        
        double dTimeNow_s = static_cast<double>(ptdDuration.total_milliseconds())/1000.0;
        
        return(dTimeNow_s);
    }
    
    void uxas::common::utilities::c_TimeUtilities::GetTimeNow(n_POSIX_TIME::ptime& ptimeTimeNow)
    {
        ptimeTimeNow = n_POSIX_TIME::microsec_clock::universal_time() + tmdrtnGetTimeCorrection();
    }
    n_POSIX_TIME::ptime uxas::common::utilities::c_TimeUtilities::ptGetTimeNow()
    {
        return(n_POSIX_TIME::microsec_clock::universal_time() + tmdrtnGetTimeCorrection());
    }
    
    std::string uxas::common::utilities::c_TimeUtilities::strGetTimeNow()
    {
        boost::posix_time::time_facet *output_facet = new boost::posix_time::time_facet();
        std::stringstream sstrTimeString;
        sstrTimeString.imbue(std::locale(sstrTimeString.getloc(), output_facet));
        output_facet->format("%Y_%m_%d__%H_%M_%S%F");    // eg. 2014_01_16__18_36_45.893911
//        output_facet->format("%Y-%m-%d_%H-%M-%S");    // eg. 2014-01-16_18-36-45
        sstrTimeString << ptGetTimeNow();
        return(sstrTimeString.str());
    }
    
    std::string uxas::common::utilities::c_TimeUtilities::strGetTimeCorrection()
    {
        std::stringstream sstrTimeString;
        sstrTimeString << tmdrtnGetTimeCorrection().total_milliseconds()%10000;
        return(sstrTimeString.str());
    }
    
    n_POSIX_TIME::ptime uxas::common::utilities::c_TimeUtilities::ptGetTimeFromSeconds(uint32_t uiTime_s)
    {
        return(ptimeGetTime_Jan_01_1970() + n_POSIX_TIME::time_duration(0, 0,uiTime_s));
    }

    
}; //namespace log
}; //namespace common
}; //namespace uxas

