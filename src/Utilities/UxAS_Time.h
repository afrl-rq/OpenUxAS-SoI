// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#ifndef UXAS_COMMON_TIME_H
#define UXAS_COMMON_TIME_H

#include <atomic>
#include <chrono>
#include <memory>
#include <mutex>
#include <cstdint>
#include <string>

namespace uxas
{
namespace common
{

class Time
{
public:

    enum TimeMode
    {
        REAL_TIME,
        DISCRETE_TIME
    };
public:

    /**
     * 365.25×24×3600×10⁹ = 31 557 600 000 000 000 (nanoseconds in leap-year averaged year)
     * int64_t:  2^63 = 9 223 372 036 854 775 808
     * 9223372036854775808 ÷ 31557600000000000 = 292.271023045 years
     */

    /** \brief Time utility class.
     * 
     * @return reference to singleton Time instance.
     */
    static Time&
    getInstance();

    // \brief do not call constructor directly using singleton pattern

    Time() { };

private:

    // \brief Prevent copy construction
    Time(Time const&) = delete;

    // \brief Prevent copy assignment operation
    void operator=(Time const&) = delete;

    static std::unique_ptr<Time> s_instance;

public:

    // <editor-fold defaultstate="collapsed" desc="Epoch time functions">

    /**\brief Hours since time 00:00:00 January 1, 1970.
     * 
     * @return Hour count between 00:00:00 January 1, 1970 and now.  
     * Hour count may be externally calibrated; can invoke isExternallyCalibrated and/or 
     * getTimeLastExternalCalibrationSinceEpoch_ms functions for more information.
     */
    virtual int64_t
    getUtcTimeSinceEpoch_hr()
    {
        std::lock_guard<std::mutex> lock(m_calibrationMutex);
        return std::chrono::duration_cast<std::chrono::hours>
                (std::chrono::system_clock::now().time_since_epoch()).count()
                + (m_timeExternalCalibrationDelta_ms / (3600 * 1000));
    };

    /**\brief Minutes since time 00:00:00 January 1, 1970.
     * 
     * @return Minute count between 00:00:00 January 1, 1970 and now.  
     * Minute count may be externally calibrated; can invoke isExternallyCalibrated and/or 
     * getTimeLastExternalCalibrationSinceEpoch_ms functions for more information.
     */
    virtual int64_t
    getUtcTimeSinceEpoch_min()
    {
        std::lock_guard<std::mutex> lock(m_calibrationMutex);
        return std::chrono::duration_cast<std::chrono::minutes>
                (std::chrono::system_clock::now().time_since_epoch()).count()
                + (m_timeExternalCalibrationDelta_ms / (60 * 1000));
    };

    /**\brief Seconds since time 00:00:00 January 1, 1970.
     * 
     * @return Second count between 00:00:00 January 1, 1970 and now.  
     * Second count may be externally calibrated; can invoke isExternallyCalibrated and/or 
     * getTimeLastExternalCalibrationSinceEpoch_ms functions for more information.
     */
    virtual int64_t
    getUtcTimeSinceEpoch_s()
    {
        std::lock_guard<std::mutex> lock(m_calibrationMutex);
        return std::chrono::duration_cast<std::chrono::seconds>
                (std::chrono::system_clock::now().time_since_epoch()).count()
                + (m_timeExternalCalibrationDelta_ms / 1000);
    };

    /**\brief Milliseconds since time 00:00:00 January 1, 1970.
     * 
     * @return Millisecond count between 00:00:00 January 1, 1970 and now.  
     * Millisecond count may be externally calibrated; can invoke isExternallyCalibrated and/or 
     * getTimeLastExternalCalibrationSinceEpoch_ms functions for more information.
     */
    virtual int64_t
    getUtcTimeSinceEpoch_ms()
    {
        std::lock_guard<std::mutex> lock(m_calibrationMutex);
        int64_t time_ms = std::chrono::duration_cast<std::chrono::milliseconds>
                (std::chrono::system_clock::now().time_since_epoch()).count()
                + m_timeExternalCalibrationDelta_ms;
        return (time_ms);
    };

    /**\brief Microseconds since time 00:00:00 January 1, 1970.
     * 
     * @return Microsecond count between 00:00:00 January 1, 1970 and now.  
     * Microsecond count comes directly from CPU clock (never externally calibrated).
     */
    virtual int64_t
    getUtcCpuTimeSinceEpoch_us()
    {
        return std::chrono::duration_cast<std::chrono::microseconds>
                (std::chrono::system_clock::now().time_since_epoch()).count();
    };

    /**\brief Nanoseconds since time 00:00:00 January 1, 1970.
     * 
     * @return Nanosecond count between 00:00:00 January 1, 1970 and now.  
     * Nanosecond count comes directly from CPU clock (never externally calibrated).
     */
    virtual int64_t
    getUtcCpuTimeSinceEpoch_ns()
    {
        return std::chrono::duration_cast<std::chrono::nanoseconds>
                (std::chrono::system_clock::now().time_since_epoch()).count();
    };
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Start time functions">

    /**\brief Time in hours of class initialization relative to 00:00:00 January 1, 1970.
     * 
     * @return Hour count between 00:00:00 January 1, 1970 and time of class initialization.  
     * Hour count may be externally calibrated; can invoke isExternallyCalibrated and/or 
     * getTimeLastExternalCalibrationSinceEpoch_ms functions for more information.
     */
    virtual int64_t
    getUtcStartTimeSinceEpoch_hr()
    {
        std::lock_guard<std::mutex> lock(m_calibrationMutex);
        return (m_cpuStartTimeSinceEpoch_hr + (m_timeExternalCalibrationDelta_ms / (3600 * 1000)));
    };

    /**\brief Time in minutes of class initialization relative to 00:00:00 January 1, 1970.
     * 
     * @return Minute count between 00:00:00 January 1, 1970 and time of class initialization.  
     * Minute count may be externally calibrated; can invoke isExternallyCalibrated and/or 
     * getTimeLastExternalCalibrationSinceEpoch_ms functions for more information.
     */
    virtual int64_t
    getUtcStartTimeSinceEpoch_min()
    {
        std::lock_guard<std::mutex> lock(m_calibrationMutex);
        return (m_cpuStartTimeSinceEpoch_min + (m_timeExternalCalibrationDelta_ms / (60 * 1000)));
    };

    /**\brief Time in seconds of class initialization relative to 00:00:00 January 1, 1970.
     * 
     * @return Second count between 00:00:00 January 1, 1970 and time of class initialization.  
     * Second count may be externally calibrated; can invoke isExternallyCalibrated and/or 
     * getTimeLastExternalCalibrationSinceEpoch_ms functions for more information.
     */
    virtual int64_t
    getUtcStartTimeSinceEpoch_s()
    {
        std::lock_guard<std::mutex> lock(m_calibrationMutex);
        return (m_cpuStartTimeSinceEpoch_s + (m_timeExternalCalibrationDelta_ms / 1000));
    };

    /**\brief Time in milliseconds of class initialization relative to 00:00:00 January 1, 1970.
     * 
     * @return Millisecond count between 00:00:00 January 1, 1970 and time of class initialization.  
     * Hour count may be externally calibrated; can invoke isExternallyCalibrated and/or 
     * getTimeLastExternalCalibrationSinceEpoch_ms functions for more information.
     */
    virtual int64_t
    getUtcStartTimeSinceEpoch_ms()
    {
        std::lock_guard<std::mutex> lock(m_calibrationMutex);
        return (m_cpuStartTimeSinceEpoch_ms + m_timeExternalCalibrationDelta_ms);
    };

    /**\brief Time in microseconds of class initialization relative to 00:00:00 January 1, 1970.
     * 
     * @return Microsecond count between 00:00:00 January 1, 1970 and time of class initialization.  
     * Microsecond count directly derived from CPU clock calculations (never externally calibrated).
     */
    virtual int64_t
    getUtcCpuStartTimeSinceEpoch_us()
    {
        return (m_cpuStartTimeSinceEpoch_us);
    };

    /**\brief Time in nanoseonds of class initialization relative to 00:00:00 January 1, 1970.
     * 
     * @return Nanoseond count between 00:00:00 January 1, 1970 and time of class initialization.  
     * Nanosecond count directly derived from CPU clock calculations (never externally calibrated).
     */
    virtual int64_t
    getUtcCpuStartTimeSinceEpoch_ns()
    {
        return (m_cpuStartTimeSinceEpoch_ns);
    };
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Duration since start time functions">    

    /**\brief Duration in hours since class initialization.
     * 
     * @return Hour count between time of initialization of this class and now.  
     */
    virtual int64_t
    getDurationSinceStart_hr()
    {
        return (std::chrono::duration_cast<std::chrono::hours>
                (std::chrono::system_clock::now().time_since_epoch()).count()
                - m_cpuStartTimeSinceEpoch_hr);
    };

    /**\brief Duration in minutes since class initialization.
     * 
     * @return Minute count between time of initialization of this class and now.  
     */
    virtual int64_t
    getDurationSinceStart_min()
    {
        return (std::chrono::duration_cast<std::chrono::minutes>
                (std::chrono::system_clock::now().time_since_epoch()).count()
                - m_cpuStartTimeSinceEpoch_min);
    };

    /**\brief Duration in seconds since class initialization.
     * 
     * @return Second count between time of initialization of this class and now.  
     */
    virtual int64_t
    getDurationSinceStart_s()
    {
        return (std::chrono::duration_cast<std::chrono::seconds>
                (std::chrono::system_clock::now().time_since_epoch()).count()
                - m_cpuStartTimeSinceEpoch_s);
    };

    /**\brief Duration in milliseconds since class initialization.
     * 
     * @return Millisecond count between time of initialization of this class and now.  
     */
    virtual int64_t
    getDurationSinceStart_ms()
    {
        return (std::chrono::duration_cast<std::chrono::milliseconds>
                (std::chrono::system_clock::now().time_since_epoch()).count()
                - m_cpuStartTimeSinceEpoch_ms);
    };

    /**\brief Microseconds since class initialization.
     * 
     * @return Microsecond count between time of initialization of this class and now.  
     */
    virtual int64_t
    getDurationSinceStart_us()
    {
        return (std::chrono::duration_cast<std::chrono::microseconds>
                (std::chrono::system_clock::now().time_since_epoch()).count()
                - m_cpuStartTimeSinceEpoch_us);
    };

    /**\brief Nanoseconds since class initialization.
     * 
     * @return Nanosecond count between time of initialization of this class and now.  
     */
    virtual int64_t
    getDurationSinceStart_ns()
    {
        return (std::chrono::duration_cast<std::chrono::nanoseconds>
                (std::chrono::system_clock::now().time_since_epoch()).count()
                - m_cpuStartTimeSinceEpoch_ns);
    };
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="External calibration functions">

    /**\brief Number of occurrences of external calibration.
     * 
     * @return External calibration count.
     */
    uint32_t
    getExternalCalibrationCount()
    {
        std::lock_guard<std::mutex> lock(m_calibrationMutex);
        return (m_timeExternallyCalibrationCount);
    };

    /**\brief Calibrates UxAS time with provided UTC reference time (calculates an
     * offset value relative to system clock).  First invocation sets host system 
     * software and hardware clocks.
     * 
     * @param year
     * @param month
     * @param day
     * @param hour
     * @param minutes
     * @param seconds
     * @param milliseconds
     * @return true if calibration succeeds; false if calibration fails.
     */
    bool
    calibrateWithReferenceUtcTime(int year, int month, int day, int hour, int minutes, int seconds, int milliseconds);

    /**\brief Calibrates UxAS time with provided UTC reference time (calculates an
     * offset value relative to system clock).  First invocation sets host system 
     * software and hardware clocks.
     * 
     * @param year
     * @param month
     * @param day
     * @param weeks time duration in whole weeks to be added to date implied by year, month, day parameters
     * @param milliseconds millisecond time duration to be added to date implied by year, month, day, weeks parameters
     * @return true if calibration succeeds; false if calibration fails.
     */
    bool
    calibrateWithReferenceUtcTime(int year, int month, int day, int weeks, int milliseconds);

private:

    bool
    calibrateWithReferenceUtcTimeImpl(int year, int month, int day, int weeks, int hour, int minutes, int seconds, int milliseconds);
    // </editor-fold>

protected:

    std::mutex m_calibrationMutex;
    uint64_t m_minimumCalibrationYear{2016};
    bool m_isSetSwHdwDateTime{false};
    std::atomic<bool> m_isSetSwHdwDateTimeLogged{false};
    std::string m_setSwHdwDateTime = "";
    uint64_t m_timeExternallyCalibrationCount{0};
    int64_t m_timeExternalCalibrationDelta_ms{0};

    uint64_t m_timeExternalCalibrationLogCount{1000};
    uint64_t m_timeExternalCalibrationLogCountMax{1000};

    int64_t m_cpuStartTimeSinceEpoch_hr{0};
    int64_t m_cpuStartTimeSinceEpoch_min{0};
    int64_t m_cpuStartTimeSinceEpoch_s{0};
    int64_t m_cpuStartTimeSinceEpoch_ms{0};
    int64_t m_cpuStartTimeSinceEpoch_us{0};
    int64_t m_cpuStartTimeSinceEpoch_ns{0};

public: //discrete time

    /** \brief  Sets the desired time mode, i.e. @ref m_desiredMode.
     * Note: If @ref m_desiredMode != @ref m_currentMode, then
     * the class will be reset next time the single instance is 
     * accessed.
     *  @param desiredTimeMode
     */
    static void setTimeMode(const TimeMode& desiredTimeMode)
    {
        m_desiredMode = desiredTimeMode;
    }

    /** \brief  the <B>discrete</B> time is reset by calling this function.
     * Note: this sets the start times to 0 and @ref m_discreteTime_ms to
     * <B>discreteTime_ms</B>
     *  @param discreteTime_ms
     */
    void resetDiscreteTime_ms(const int64_t& discreteTime_ms = int64_t(0))
    {
        std::lock_guard<std::mutex> lock(m_calibrationMutex);
        m_discreteTime_ms = discreteTime_ms;
        m_cpuStartTimeSinceEpoch_hr = 0;
        m_cpuStartTimeSinceEpoch_min = 0;
        m_cpuStartTimeSinceEpoch_s = 0;
        m_cpuStartTimeSinceEpoch_ms = 0;
        m_cpuStartTimeSinceEpoch_us = 0;
        m_cpuStartTimeSinceEpoch_ns = 0;
    };

    /** \brief  the current (discrete) time is set by calling this function.
     *  NOTE:: the absolute discrete time is the <B>start time<\B> + the <B>discrete time</B>
     *  @param discreteTime_ms
     */
    void setDiscreteTime_ms(const int64_t& discreteTime_ms)
    {
        std::lock_guard<std::mutex> lock(m_calibrationMutex);
        m_discreteTime_ms = discreteTime_ms;
    };

    /** \brief  retrieve the current (discrete) time
     *
     *  @return current (<B>discrete</B>) time in milliseconds
     */
    int64_t getDiscreteTime_ms()
    {
        std::lock_guard<std::mutex> lock(m_calibrationMutex);
        return (m_discreteTime_ms);
    };

protected: //discrete time 

    /** \brief The current (<B>discrete</B>) time.*/
    int64_t m_discreteTime_ms{0};

    /** \brief  keeps track of the current @ref TimeMode. */
    static TimeMode m_currentMode;

    /** \brief  This is the <B>desired</B> @ref TimeMode. 
     the @ref m_currentMode be changed to this the next
     time the single instance of this class is accessed*/
    static TimeMode m_desiredMode;
};

class DiscreteTime : public Time
{
public:
    // \brief construction is public to replace Time class (but use as a singleton pattern)

    DiscreteTime() { };
private:
    // \brief Prevent copy construction
    DiscreteTime(Time const&) = delete;

    // \brief Prevent copy assignment operation
    void operator=(DiscreteTime const&) = delete;

public:

    // <editor-fold defaultstate="collapsed" desc="Epoch time functions">

    /**\brief Hours since time 00:00:00 January 1, 1970.
     * 
     * @return Hour count between 00:00:00 January 1, 1970 and now.  
     * Hour count may be externally calibrated; can invoke isExternallyCalibrated and/or 
     * getTimeLastExternalCalibrationSinceEpoch_ms functions for more information.
     */
    virtual int64_t
    getUtcTimeSinceEpoch_hr() override
    {
        return ((getDiscreteTime_ms() / (3600 * 1000)) + m_cpuStartTimeSinceEpoch_hr);
    };

    /**\brief Minutes since time 00:00:00 January 1, 1970.
     * 
     * @return Minute count between 00:00:00 January 1, 1970 and now.  
     * Minute count may be externally calibrated; can invoke isExternallyCalibrated and/or 
     * getTimeLastExternalCalibrationSinceEpoch_ms functions for more information.
     */
    virtual int64_t
    getUtcTimeSinceEpoch_min() override
    {
        return ((getDiscreteTime_ms() / (60 * 1000)) + m_cpuStartTimeSinceEpoch_min);
    };

    /**\brief Seconds since time 00:00:00 January 1, 1970.
     * 
     * @return Second count between 00:00:00 January 1, 1970 and now.  
     * Second count may be externally calibrated; can invoke isExternallyCalibrated and/or 
     * getTimeLastExternalCalibrationSinceEpoch_ms functions for more information.
     */
    virtual int64_t
    getUtcTimeSinceEpoch_s() override
    {
        return ((getDiscreteTime_ms() / 1000) + m_cpuStartTimeSinceEpoch_s);
    };

    /**\brief Milliseconds since time 00:00:00 January 1, 1970.
     * 
     * @return Millisecond count between 00:00:00 January 1, 1970 and now.  
     * Millisecond count may be externally calibrated; can invoke isExternallyCalibrated and/or 
     * getTimeLastExternalCalibrationSinceEpoch_ms functions for more information.
     */
    virtual int64_t getUtcTimeSinceEpoch_ms() override
    {
        int64_t time_ms = getDiscreteTime_ms() + m_cpuStartTimeSinceEpoch_ms;
        return (time_ms);
    };

    /**\brief Microseconds since time 00:00:00 January 1, 1970.
     * 
     * @return Microsecond count between 00:00:00 January 1, 1970 and now.  
     * Microsecond count comes directly from CPU clock (never externally calibrated).
     */
    virtual int64_t
    getUtcCpuTimeSinceEpoch_us() override
    {
        return ((getDiscreteTime_ms() * 1000) + m_cpuStartTimeSinceEpoch_us);
    };

    /**\brief Nanoseconds since time 00:00:00 January 1, 1970.
     * 
     * @return Nanosecond count between 00:00:00 January 1, 1970 and now.  
     * Nanosecond count comes directly from CPU clock (never externally calibrated).
     */
    virtual int64_t
    getUtcCpuTimeSinceEpoch_ns() override
    {
        return ((getDiscreteTime_ms() * 1000000) + m_cpuStartTimeSinceEpoch_ns);
    };
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Duration since start time functions">    

    /**\brief Duration in hours since class initialization.
     * 
     * @return Hour count between time of initialization of this class and now.  
     */
    virtual int64_t
    getDurationSinceStart_hr() override
    {
        return (getDiscreteTime_ms() / (3600 * 1000));
    };

    /**\brief Duration in minutes since class initialization.
     * 
     * @return Minute count between time of initialization of this class and now.  
     */
    virtual int64_t
    getDurationSinceStart_min() override
    {
        return (getDiscreteTime_ms() / (60 * 1000));
    };

    /**\brief Duration in seconds since class initialization.
     * 
     * @return Second count between time of initialization of this class and now.  
     */
    virtual int64_t
    getDurationSinceStart_s() override
    {
        return (getDiscreteTime_ms() / 1000);
    };

    /**\brief Duration in milliseconds since class initialization.
     * 
     * @return Millisecond count between time of initialization of this class and now.  
     */
    virtual int64_t
    getDurationSinceStart_ms() override
    {
        return (getDiscreteTime_ms());
    };

    /**\brief Microseconds since class initialization.
     * 
     * @return Microsecond count between time of initialization of this class and now.  
     */
    virtual int64_t
    getDurationSinceStart_us() override
    {
        return (getDiscreteTime_ms() * 1000);
    };

    /**\brief Nanoseconds since class initialization.
     * 
     * @return Nanosecond count between time of initialization of this class and now.  
     */
    virtual int64_t
    getDurationSinceStart_ns() override
    {
        return (getDiscreteTime_ms() * 1000000);
    };
    // </editor-fold>

};

}; //namespace common
}; //namespace uxas

#endif /* UXAS_COMMON_TIME_H */
