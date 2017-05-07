// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   TimeUtilities.h
 * Author: steve
 *
 * Created on March 19, 2012, 12:04 PM
 */

#ifndef TIMEUTILITIES_H
#define TIMEUTILITIES_H

#include <cstdint> // uint32_t

#include <chrono>       // time functions

//#include <mutex>

#include "boost/date_time/gregorian/gregorian.hpp"
#include "boost/date_time/posix_time/posix_time.hpp"
namespace n_POSIX_TIME = boost::posix_time;

namespace uxas
{
namespace common
{
namespace utilities
{

/*! \class c_TimeUtilities
    \brief This class provides static functions to retrieve the current time in
 * different forms. It also has a functiond, @ref SetTimeCorrection_tmdrtn, to correct
 * the system clock-based time.
 * 
 */

    class mutex;

class c_TimeUtilities
{
public:
    c_TimeUtilities();
    virtual ~c_TimeUtilities(){};
    c_TimeUtilities(const c_TimeUtilities& rhs){};
    
public:
    
    static const std::chrono::microseconds _oneHundredMicroseconds;
    
    
    static uint32_t uiGetTime2030_s();
    static int64_t getTime2030_ms();
    
    static uint32_t uiGetTimeNow_s();
    static int64_t getTimeNow_ms(const bool& bCorrected=true);
    
    static double dGetTimeNow_s(const bool& bCorrected=true);
    
    static uint32_t uiGetTimeSinceStart_s();
    
    static double dGetTimeSinceStart_s();
    
    static void GetTimeNow(n_POSIX_TIME::ptime& ptimeTimeNow);
    static n_POSIX_TIME::ptime ptGetTimeNow();
    static std::string strGetTimeNow();
    static std::string strGetTimeCorrection();
    
    static n_POSIX_TIME::ptime ptGetTimeFromSeconds(uint32_t uiTime_s);
    
public:
   
    static const n_POSIX_TIME::ptime& ptimeGetTime_Jan_01_1970(){return(n_ptimeTime_Jan_01_1970);};
    static const n_POSIX_TIME::ptime& ptimeGetTime_Jan_01_2013(){return(n_ptimeTime_Jan_01_2013);};
    static const n_POSIX_TIME::ptime& ptimeGetTime_Jan_01_2030(){return(n_ptimeTime_Jan_01_2030);};
    
    static n_POSIX_TIME::ptime& ptimeGetTimeInitial(){return(m_ptimeTimeInitial);};
    
    static n_POSIX_TIME::time_duration& tmdrtnGetTimeCorrection(){return(m_tmdrtnTimeCorrection);};
    static void SetTimeCorrection_tmdrtn(n_POSIX_TIME::time_duration& tmdrtnTimeCorrection);
    
    
    static void bSetTimeCorrected_b(const bool& bTimeCorrected){m_bTimeCorrected = bTimeCorrected ;};
    static const bool& bGetTimeCorrected(){return(m_bTimeCorrected);};
    /*! \brief accessor function for: std::mutex m_mtxTimeSyncMutex */
    static mutex*& pmtxGetTimeSyncMutex() {
        return (m_pmtxTimeSyncMutex);
    };
    
protected:
    
    static const n_POSIX_TIME::ptime n_ptimeTime_Jan_01_1970;
    static const n_POSIX_TIME::ptime n_ptimeTime_Jan_01_2013;
    static const n_POSIX_TIME::ptime n_ptimeTime_Jan_01_2030;
    static n_POSIX_TIME::ptime m_ptimeTimeInitial;
    static n_POSIX_TIME::time_duration m_tmdrtnTimeCorrection; //add this correction to Computer Time, i.e. n_POSIX_TIME::microsec_clock::universal_time(), to get corrected time, e.g. GPS time
    static bool m_bTimeCorrected;
            /*! \brief  synchronize low level operations*/
    static mutex* m_pmtxTimeSyncMutex;


};

}; //namespace log
}; //namespace common
}; //namespace uxas

#endif /* TIMEUTILITIES_H */

