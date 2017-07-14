// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#include "UxAS_Time.h"

#include "UxAS_Log.h"

#include <ctime>
#include <iostream>
#include <ratio>

#define TIME_LOCAL_LOG_MESSAGE(message) std::cout << message << std::endl; std::cout.flush();

namespace uxas
{
namespace common
{

Time::TimeMode Time::m_currentMode{Time::REAL_TIME};
Time::TimeMode Time::m_desiredMode{Time::REAL_TIME};
std::unique_ptr<Time> Time::s_instance = nullptr;

Time&
Time::getInstance()
{
    // first time/one time creation
    if ((Time::s_instance == nullptr) || (m_currentMode != m_desiredMode))
    {
        switch (m_desiredMode)
        {
            case Time::DISCRETE_TIME:
                s_instance.reset(new DiscreteTime);
                break;
            default:
            case Time::REAL_TIME:
                s_instance.reset(new Time);
                break;
        } //switch(m_desiredMode)
        m_currentMode = m_desiredMode;

        s_instance->m_cpuStartTimeSinceEpoch_hr
                = std::chrono::duration_cast<std::chrono::hours>
                (std::chrono::system_clock::now().time_since_epoch()).count();
        s_instance->m_cpuStartTimeSinceEpoch_min
                = std::chrono::duration_cast<std::chrono::minutes>
                (std::chrono::system_clock::now().time_since_epoch()).count();
        s_instance->m_cpuStartTimeSinceEpoch_s
                = std::chrono::duration_cast<std::chrono::seconds>
                (std::chrono::system_clock::now().time_since_epoch()).count();
        s_instance->m_cpuStartTimeSinceEpoch_ms
                = std::chrono::duration_cast<std::chrono::milliseconds>
                (std::chrono::system_clock::now().time_since_epoch()).count();
        s_instance->m_cpuStartTimeSinceEpoch_us
                = std::chrono::duration_cast<std::chrono::microseconds>
                (std::chrono::system_clock::now().time_since_epoch()).count();
        s_instance->m_cpuStartTimeSinceEpoch_ns
                = std::chrono::duration_cast<std::chrono::nanoseconds>
                (std::chrono::system_clock::now().time_since_epoch()).count();
    }
    return *s_instance;
};

bool
Time::calibrateWithReferenceUtcTime(int year, int month, int day, int hour, int minutes, int seconds, int milliseconds)
{
    UXAS_LOG_DEBUG_VERBOSE_TIME("Time::calibrateWithReferenceUtcTime y, M, d, h, m, s, ms[", year, ",", month, ",", day, ",", hour, ",", minutes, ",", seconds, ",", milliseconds, "]");
    if (year < m_minimumCalibrationYear)
    {
        UXAS_LOG_DEBUG_VERBOSE_TIME("Time::calibrateWithReferenceUtcTime invalid year [", year, "]");
        return (false);
    }
    return (calibrateWithReferenceUtcTimeImpl(year, month, day, -1, hour, minutes, seconds, milliseconds));
};

bool
Time::calibrateWithReferenceUtcTime(int year, int month, int day, int weeks, int milliseconds)
{
    UXAS_LOG_DEBUG_VERBOSE_TIME("Time::calibrateWithReferenceUtcTime y, M, d, weeks, ms[", year, ",", month, ",", day, ",", weeks, ",", milliseconds, "]");
    if (weeks < 0)
    {
        UXAS_LOG_DEBUG_VERBOSE_TIME("Time::calibrateWithReferenceUtcTime invalid weeks [", weeks, "]");
        return (false);
    }
    return (calibrateWithReferenceUtcTimeImpl(year, month, day, weeks, 0, 0, 0, milliseconds));
};

bool
Time::calibrateWithReferenceUtcTimeImpl(int year, int month, int day, int weeks, int hour, int minutes, int seconds, int milliseconds)
{
    UXAS_LOG_DEBUG_VERBOSE_TIME("Time::calibrateWithReferenceUtcTimeImpl - START");

    int64_t nowTimeSinceEpoch_ms = std::chrono::duration_cast<std::chrono::milliseconds>
            (std::chrono::system_clock::now().time_since_epoch()).count();
    UXAS_LOG_DEBUG_VERBOSE_TIME("Time::calibrateWithReferenceUtcTimeImpl nowTimeSinceEpoch_ms [", nowTimeSinceEpoch_ms, "]");

    std::tm dateTm = {0};
    dateTm.tm_isdst = -1;

    dateTm.tm_year = year - 1900; // year since 1900
    std::time_t tmtNow = std::time(nullptr);
#ifdef _WIN32
    std::tm tmNow;
    gmtime_s(&tmNow, &tmtNow);
#else
    std::tm* tmNow = gmtime(&tmtNow);
#endif

    UXAS_LOG_DEBUG_VERBOSE_TIME("Time::calibrateWithReferenceUtcTimeImpl dateTm.tm_year [", dateTm.tm_year, "]");

    if (month > 0 && month < 13)
    {
        dateTm.tm_mon = month - 1; // 0-11
        UXAS_LOG_DEBUG_VERBOSE_TIME("Time::calibrateWithReferenceUtcTimeImpl dateTm.tm_mon [", dateTm.tm_mon, "]");
    }
    else
    {
        UXAS_LOG_DEBUG_VERBOSE_TIME("Time::calibrateWithReferenceUtcTimeImpl invalid month [", month, "]");
        return (false);
    }

    if (day > 0 && day < 32)
    {
        dateTm.tm_mday = day; // 1-31
        UXAS_LOG_DEBUG_VERBOSE_TIME("Time::calibrateWithReferenceUtcTimeImpl dateTm.tm_mday [", dateTm.tm_mday, "]");
    }
    else
    {
        UXAS_LOG_DEBUG_VERBOSE_TIME("Time::calibrateWithReferenceUtcTimeImpl invalid day [", day, "]");
        return (false);
    }

    if (weeks < 0) // ignore weeks; use hour, minutes, seconds
    {
        if (hour > -1 && hour < 24)
        {
            dateTm.tm_hour = hour; // 00-23
            UXAS_LOG_DEBUG_VERBOSE_TIME("Time::calibrateWithReferenceUtcTimeImpl dateTm.tm_hour [", dateTm.tm_hour, "]");
        }
        else
        {
            UXAS_LOG_DEBUG_VERBOSE_TIME("Time::calibrateWithReferenceUtcTimeImpl invalid hour [", hour, "]");
            return (false);
        }

        if (minutes > -1 && minutes < 60)
        {
            dateTm.tm_min = minutes; // 00-59
            UXAS_LOG_DEBUG_VERBOSE_TIME("Time::calibrateWithReferenceUtcTimeImpl dateTm.tm_min [", dateTm.tm_min, "]");
        }
        else
        {
            UXAS_LOG_DEBUG_VERBOSE_TIME("Time::calibrateWithReferenceUtcTimeImpl invalid minutes [", minutes, "]");
            return (false);
        }

        if (seconds > -1 && seconds < 61)
        {
            dateTm.tm_sec = seconds; // 00-60
            UXAS_LOG_DEBUG_VERBOSE_TIME("Time::calibrateWithReferenceUtcTimeImpl dateTm.tm_sec [", dateTm.tm_sec, "]");
        }
        else
        {
            UXAS_LOG_DEBUG_VERBOSE_TIME("Time::calibrateWithReferenceUtcTimeImpl invalid seconds [", seconds, "]");
            return (false);
        }
    }
    else // use weeks (later); ignore hour, minutes, seconds; 
    {
        UXAS_LOG_DEBUG_VERBOSE_TIME("Time::calibrateWithReferenceUtcTimeImpl weeks [", weeks, "]; ignoring hour, minutes, seconds");
        dateTm.tm_hour = 0;
        dateTm.tm_min = 0;
        dateTm.tm_sec = 0;
    }

    // convert std::tm to std::time_t
#ifdef _WIN32
    std::time_t dateTime = _mkgmtime(&dateTm); // UTC time (not mktime - not local time)
#else
    std::time_t dateTime = timegm(&dateTm); // UTC time (not mktime - not local time)
#endif

    // convert std::time_t to std::chrono::system_clock::time_point
    std::chrono::system_clock::time_point refTime
            = std::chrono::system_clock::from_time_t(dateTime);

    int64_t refTimeSinceEpoch_ms;
    if (weeks < 0) // ignore weeks
    {
        UXAS_LOG_DEBUG_VERBOSE_TIME("Time::calibrateWithReferenceUtcTimeImpl hour, minutes, seconds calculation");
        refTimeSinceEpoch_ms = std::chrono::duration_cast<std::chrono::milliseconds>
                (refTime.time_since_epoch()).count() + milliseconds;
    }
    else // use weeks
    {
        UXAS_LOG_DEBUG_VERBOSE_TIME("Time::calibrateWithReferenceUtcTimeImpl weeks calculation");
        uint64_t weeks_ms = static_cast<int64_t> (weeks) * 7 * 24 * 3600 * 1000;
        refTimeSinceEpoch_ms = std::chrono::duration_cast<std::chrono::milliseconds>
                (refTime.time_since_epoch()).count() + weeks_ms + milliseconds;
    }
    UXAS_LOG_DEBUG_VERBOSE_TIME("Time::calibrateWithReferenceUtcTimeImpl refTimeSinceEpoch_ms [", refTimeSinceEpoch_ms, "]");

    uint64_t refTimeSinceEpoch_s = refTimeSinceEpoch_ms / 1000;
    std::chrono::time_point<std::chrono::system_clock> epochTm;
    std::chrono::time_point<std::chrono::system_clock> refCalChronoTmNoMs = epochTm + std::chrono::seconds(refTimeSinceEpoch_s);
    std::time_t refCalTtNoMs = std::chrono::system_clock::to_time_t(refCalChronoTmNoMs);
    std::tm* refCalTmNoMs = gmtime(&refCalTtNoMs);

    if ((refCalTmNoMs->tm_year + 1900) < m_minimumCalibrationYear)
    {
        UXAS_LOG_DEBUG_VERBOSE_TIME("Time::calibrateWithReferenceUtcTimeImpl invalid year [", year, "]");
        return (false);
    }

    m_calibrationMutex.lock();
    bool isCalculateDeltaMs = true;
#ifdef ICET_ARM // only change clock on gumstix or ODROID
    if (m_setSwHdwDateTime.empty())
    {
        isCalculateDeltaMs = false;
    }
#endif
    if (isCalculateDeltaMs)
    {
        m_timeExternalCalibrationDelta_ms = refTimeSinceEpoch_ms - nowTimeSinceEpoch_ms;
        if (m_timeExternallyCalibrationCount < UINT64_MAX)
        {
            m_timeExternallyCalibrationCount++;
        }
        m_calibrationMutex.unlock();

        //36 times in one hour  100s == 100000ms  100000/50 = 2000
        //50ms => 20Hz => 72000/hour
        //72/hour => 1000
        if (m_timeExternalCalibrationLogCount < m_timeExternalCalibrationLogCountMax)
        {
            m_timeExternalCalibrationLogCount++;
        }
        else
        {
            UXAS_LOG_INFORM("Time::calibrateWithReferenceUtcTimeImpl m_timeExternalCalibrationDelta_ms [", m_timeExternalCalibrationDelta_ms, "]");
            m_timeExternalCalibrationLogCount = 0;
        }
        UXAS_LOG_DEBUG_VERBOSE_TIME("Time::calibrateWithReferenceUtcTimeImpl - END (delta calculation)");
        return (true);
    }

    // set host system software and hardware clocks (*nix specific)
#ifdef ICET_ARM // only change clock on gumstix or ODROID
    if (m_setSwHdwDateTime.empty())
    {
#ifdef DEBUG_VERBOSE_LOGGING_ENABLED_TIME
        TIME_LOCAL_LOG_MESSAGE("Time::calibrateWithReferenceUtcTimeImpl setting system software clock and hardware clock");
#endif

        if (weeks < 0) // ignore weeks
        {
#ifdef DEBUG_VERBOSE_LOGGING_ENABLED_TIME
            TIME_LOCAL_LOG_MESSAGE("Time::calibrateWithReferenceUtcTimeImpl setting system and hardware clock using hour, minutes, seconds parameters");
#endif
            m_setSwHdwDateTime = std::to_string(year) + "-" + std::to_string(month) + "-" + std::to_string(day) + " " + std::to_string(hour) + ":" + std::to_string(minutes) + ":" + std::to_string(seconds) + "." + std::to_string(milliseconds);
        }
        else
        {
#ifdef DEBUG_VERBOSE_LOGGING_ENABLED_TIME
            TIME_LOCAL_LOG_MESSAGE("Time::calibrateWithReferenceUtcTimeImpl setting system and hardware clock using weeks parameter");
#endif
            uint64_t refTimeSinceEpochMsOnly_ms = refTimeSinceEpoch_ms - (refTimeSinceEpoch_s * 1000);
            m_setSwHdwDateTime = std::to_string(refCalTmNoMs->tm_year + 1900) + "-" + std::to_string(refCalTmNoMs->tm_mon + 1) + "-" + std::to_string(refCalTmNoMs->tm_mday) + " " + std::to_string(refCalTmNoMs->tm_hour) + ":" + std::to_string(refCalTmNoMs->tm_min) + ":" + std::to_string(refCalTmNoMs->tm_sec) + "." + std::to_string(refTimeSinceEpochMsOnly_ms);
        }

#ifdef DEBUG_VERBOSE_LOGGING_ENABLED_TIME
        TIME_LOCAL_LOG_MESSAGE("Time::calibrateWithReferenceUtcTimeImpl invoking system call with date time string [" << m_setSwHdwDateTime << "]");
#endif
        //m_setSwHdwDateTime="2016-06-22 01:02:03.456"
        std::string sysCmd = "nohup $((date --set='" + m_setSwHdwDateTime + "' && date --rfc-3339=ns > /dev/null 2>&1) && (hwclock -w > /dev/null 2>&1) && (disown > /dev/null 2>&1)) > /dev/null 2>&1";
        std::system(sysCmd.c_str());

        m_isSetSwHdwDateTime = true;
        if (m_timeExternallyCalibrationCount < UINT64_MAX)
        {
            m_timeExternallyCalibrationCount++;
        }
    }
#endif // only change clock on gumstix or ODROID

    m_calibrationMutex.unlock();

    if (m_isSetSwHdwDateTime && !m_isSetSwHdwDateTimeLogged)
    {
        UXAS_LOG_INFORM("Time::calibrateWithReferenceUtcTimeImpl invoked system call with date time string [", m_setSwHdwDateTime, "]");
        m_isSetSwHdwDateTimeLogged = true;
    }

    UXAS_LOG_DEBUG_VERBOSE_TIME("Time::calibrateWithReferenceUtcTimeImpl - END (update system)");
    return (true);
};

}; //namespace common
}; //namespace uxas

int64_t get_utc_time_since_epoch_ms() {
  return uxas::common::Time::getInstance().getUtcTimeSinceEpoch_ms();
}
