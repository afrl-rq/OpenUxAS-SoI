// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#ifndef UXAS_COMMON_TIMER_MANAGER_H
#define UXAS_COMMON_TIMER_MANAGER_H

#include <thread>
#include <memory>
#include <mutex>
#include <condition_variable>
#include <algorithm>
#include <functional>
#include <chrono>
#include <unordered_map>
#include <set>
#include <cstdint>
#include <string>
#include <vector>

namespace uxas
{
namespace common
{

/** \class TimerManager
 * 
 * @par Description:
 * The <B><i>TimerManager</i></B> manages zero to many Timer objects with a single thread.
 * 
 * @n
 */
class TimerManager
{
private:

    struct Timer
    {
        Timer() noexcept { };

        template<typename Tfunction>
        Timer(Tfunction&& handler, const std::string& name) noexcept
        : m_name(name), m_handler(std::forward<Tfunction>(handler)) { };

        Timer(Timer const& r) = delete;

        Timer(Timer&& rhs) noexcept
        : m_id(rhs.m_id), m_name(rhs.m_name), m_nextCallbackTime(rhs.m_nextCallbackTime), m_period_ms(rhs.m_period_ms),
        m_handler(std::move(rhs.m_handler)), m_isExecutingCallback(rhs.m_isExecutingCallback),
        m_isDisabled(rhs.m_isDisabled), m_isToBeDestroyed(rhs.m_isToBeDestroyed) { };

        Timer& operator=(Timer const& r) = delete;

        Timer& operator=(Timer&& rhs)
        {
            if (this != &rhs)
            {
                m_id = rhs.m_id;
                m_name = rhs.m_name;
                m_nextCallbackTime = rhs.m_nextCallbackTime;
                m_period_ms = rhs.m_period_ms;
                m_handler = std::move(rhs.m_handler);
                m_isExecutingCallback = rhs.m_isExecutingCallback;
                m_isDisabled = rhs.m_isDisabled;
                m_isToBeDestroyed = rhs.m_isToBeDestroyed;
            }
            return *this;
        };

        uint64_t m_id{0};
        std::string m_name;
        std::chrono::time_point<std::chrono::system_clock> m_nextCallbackTime;
        std::chrono::milliseconds m_period_ms{0};
        std::function<void() > m_handler;
        bool m_isExecutingCallback{false};
        bool m_isDisabled{false};
        bool m_isToBeDestroyed{false};
    };

    /** Comparison functor to sort the timer "queue" by Timer::nextTimePoint */
    struct NextActiveTimerComparator
    {

        bool operator()(const Timer &a, const Timer &b) const
        {
            return a.m_nextCallbackTime < b.m_nextCallbackTime;
        }
    };

public:

    static const std::string&
    s_typeName() { static std::string s_string("TimerManager"); return (s_string); };

    static TimerManager&
    getInstance();

    ~TimerManager();

private:

    // \brief Prevent direct, public construction (singleton pattern)
    TimerManager();

    // \brief Prevent copy construction
    TimerManager(TimerManager const&) = delete;

    // \brief Prevent copy assignment operation
    void operator=(TimerManager const&) = delete;

    void
    initialize();

public:

    /** \brief Creates a new timer.
     * 
     * @param handler is callback function (e.g., std::bind(classname::function, this)).
     * @param name string used in log messages
     * @return identifier for created timer.
     */
    uint64_t
    createTimer(const std::function<void()> &handler, const std::string& name);

    /** \brief Creates a new timer.
     * 
     * @param handler is callback function (e.g., std::bind(&classname::function, this)).
     * @param name string used in log messages
     * @return identifier for created timer.
     */
    uint64_t
    createTimer(std::function<void()>&& handler, const std::string& name);

    /** \brief Start timer in single-shot mode.
     * 
     * @param timerId identifier for timer to be started.
     * @param singleShotDuration_ms duration of time in milliseconds to wait relative 
     * to function call time to invoke callback.
     * @return true indicates successful single-shot timer start
     */
    bool
    startSingleShotTimer(uint64_t timerId, uint64_t singleShotDuration_ms);

    /** \brief Start timer in periodic mode.
     * 
     * @param timerId identifier for timer to be started.
     * @param startDelayFromNow_ms duration of time >0 relative to function call time 
     * to wait before beginning periodic callback invocation (first callback occurs
     * at time = now + startDelayFromNow_ms).
     * @param period_ms duration of time between repetitive callbacks.
     * @return true indicates successful periodic timer start
     */
    bool
    startPeriodicTimer(uint64_t timerId, uint64_t startDelayFromNow_ms, uint64_t period_ms);

    /** \brief Check to see if a timer is active/running
     * 
     * @param timerId identifier for timer to be check for active state
     * @return true indicates that timer is active, false indicates that timer
     * callback will not be called until activated via a start timer call
     */
    bool
    isTimerActive(uint64_t timerId);

    /** \brief Disable (not destroy) timer; timer can be started or destroyed later.
     * 
     * @param timerId identifier for timer to be disabled.
     * @param timeOut_ms Duration in milliseconds for caller to wait for completion of timer disable.  
     * Recommended value is three times the timer's duration (single-shot timer) or timer's period (periodic timer).
     * @return true if timer is disabled; false if timer will be disabled after completing 
     * its current callback; false if timer identifier is invalid.
     */
    bool
    disableTimer(uint64_t timerId, uint64_t timeOut_ms);

    /** \brief Destroy timer.
     * 
     * @param timerId identifier for timer to be destroyed.
     * @param timeOut_ms Duration in milliseconds for caller to wait for destruction of timer.
     * Recommended value is three times the timer's duration (single-shot timer) or timer's period (periodic timer).
     * @return true if timer is destroyed; false if timer will be destroyed after completing 
     * its current callback; false if timer identifier is invalid.
     */
    bool
    destroyTimer(uint64_t timerId, uint64_t timeOut_ms);

    /** \brief Destroy timers.
     * 
     * @param timerIds identifiers for timers to be destroyed.
     * @param timeOut_ms Duration in milliseconds for caller to wait for destruction of timers.
     * Recommended value is three times largest duration (single-shot timer) or timer's period (periodic timer) for all of the timers.
     * @return number of destroyed timers; if returned value is less than the size of the vector of IDs, 
     * then zero or more timers will be destroyed later (after completing an active callback) 
     * and zero or more timer identifiers are invalid.
     */
    uint64_t
    destroyTimers(std::vector<uint64_t>& timerIds, uint64_t timeOut_ms);

private:

    void
    executeManagement();

    uint64_t
    createTimerImpl(Timer&& timer);

    bool
    startTimerImpl(uint64_t timerId, uint64_t startDelayFromNow_ms, uint64_t period_ms);

    /** \brief Disables or destroys a managed <B><i>Timer</i></B>.
     * @par Usage: Lock mutex (e.g., std::unique_lock<std::mutex> lock(m_mutex);) 
     * before calling this private function to achieve thread-safety.
     *  
     * @param timerId
     * @param isDestroy
     * @param timeOut_ms
     * @return 
     */
    bool
    disableOrDestroyTimerImpl(uint64_t timerId, bool isDestroy, uint64_t period_ms);

    /** \brief Disables or destroys a managed <B><i>Timer</i></B>.
     * @par Usage: Lock mutex (e.g., std::unique_lock<std::mutex> lock(m_mutex);) 
     * before calling this function for thread-safety.
     *  
     * @param timerId
     * @param isDestroy
     * @return 
     */
    bool
    disableOrDestroyExistingTimerImpl(uint64_t timerId, Timer& timer, bool isDestroy);

    static std::unique_ptr<TimerManager> s_instance;

    std::mutex m_mutex;
    std::condition_variable m_wakeUp;
    std::thread m_workerThread;
    bool m_isFinished{false};
    uint64_t m_nextId{1};
    std::chrono::milliseconds m_timeDurationReattempt_ms{10};

    NextActiveTimerComparator m_comparator;
    // Queue is a set of references to Timer objects, sorted by next
    std::multiset<std::reference_wrapper<Timer>, NextActiveTimerComparator> m_queue;
    std::unordered_map<uint64_t, Timer> m_timersById;
};

}; //namespace common
}; //namespace uxas

#endif /* UXAS_COMMON_TIMER_MANAGER_H */
