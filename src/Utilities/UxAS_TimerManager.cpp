// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#include "UxAS_TimerManager.h"

#include "UxAS_Log.h"

namespace uxas
{
namespace common
{

std::unique_ptr<TimerManager> TimerManager::s_instance = nullptr;

TimerManager&
TimerManager::getInstance()
{
    // first time/one time creation
    if (TimerManager::s_instance == nullptr)
    {
        s_instance.reset(new TimerManager);
        s_instance->initialize();
    }
    return *s_instance;
};

TimerManager::TimerManager()
: m_queue(m_comparator)
{
};

TimerManager::~TimerManager()
{
    std::unique_lock<std::mutex> lock(m_mutex);
    m_isFinished = true;
    m_wakeUp.notify_all();
    lock.unlock();
    m_workerThread.join();
};

void
TimerManager::initialize()
{
    std::unique_lock<std::mutex> lock(m_mutex);
    m_workerThread = std::thread(std::bind(&TimerManager::executeManagement, this));
};

uint64_t
TimerManager::createTimer(const std::function<void()> &handler, const std::string& name)
{
    uint64_t timerId = createTimerImpl(Timer(handler, name));
    UXAS_LOG_INFORM(s_typeName(), "::createTimer created timer having (&) handler with ID ", timerId, " and name ", name);
    return (timerId);
};

uint64_t
TimerManager::createTimer(std::function<void()>&& handler, const std::string& name)
{
    uint64_t timerId = createTimerImpl(Timer(std::move(handler), name));
    UXAS_LOG_INFORM(s_typeName(), "::createTimer created timer having (&&) handler with ID ", timerId, " and name ", name);
    return (timerId);
};

bool
TimerManager::startSingleShotTimer(uint64_t timerId, uint64_t singleShotDuration_ms)
{
    return (startTimerImpl(timerId, singleShotDuration_ms, 0));
};

bool
TimerManager::startPeriodicTimer(uint64_t timerId, uint64_t startDelayFromNow_ms, uint64_t period_ms)
{
    if (period_ms > 0)
    {
        return (startTimerImpl(timerId, startDelayFromNow_ms, period_ms));
    }
    else
    {
        UXAS_LOG_WARN(s_typeName(), "::startPeriodicTimer failed to start timer with invalid period_ms value ", period_ms);
        return (false);
    }
};

bool
TimerManager::isTimerActive(uint64_t timerId)
{
    std::unique_lock<std::mutex> lock(m_mutex);
    
    // ensure that timer has been initialized
    if (m_timersById.find(timerId) == m_timersById.end())
    {
        // Timer was destroyed or never initialized
        UXAS_LOG_WARN(s_typeName(), "::isTimerActive attempted to reference destroyed or uninitialized timer ID ", timerId);
        return (false);
    }
    
    // timer exists, check to see if it is in the timing queue
    auto queuedTimer = m_queue.find(std::ref(m_timersById.find(timerId)->second));
    if (queuedTimer != m_queue.end())
        return (true);
    
    // not in queue, report in-active
    return (false);
};

bool
TimerManager::disableTimer(uint64_t timerId, uint64_t timeOut_ms)
{
    std::unique_lock<std::mutex> lock(m_mutex);
    return (disableOrDestroyTimerImpl(timerId, false, timeOut_ms));
};

bool
TimerManager::destroyTimer(uint64_t timerId, uint64_t timeOut_ms)
{
    std::unique_lock<std::mutex> lock(m_mutex);
    return (disableOrDestroyTimerImpl(timerId, true, timeOut_ms));
};

uint64_t
TimerManager::destroyTimers(std::vector<uint64_t>& timerIds, uint64_t timeOut_ms)
{
    std::unique_lock<std::mutex> lock(m_mutex);
    auto startTime = std::chrono::system_clock::now();
    uint64_t destroyedTimersCount;
    while (true)
    {
        destroyedTimersCount = 0;
        for (auto itTimerId = timerIds.cbegin(), endItTimerId = timerIds.cend();
                itTimerId != endItTimerId; itTimerId++)
        {
            if (disableOrDestroyTimerImpl(*itTimerId, true, 0))
            {
                destroyedTimersCount++;
            }
        }
        if (destroyedTimersCount >= timerIds.size())
        {
            break;
        }
        else if (std::chrono::duration_cast<std::chrono::milliseconds>(
                std::chrono::system_clock::now() - startTime).count() > static_cast<int64_t>(timeOut_ms))
        {
            break;
        }
        std::this_thread::sleep_for(m_timeDurationReattempt_ms);
    }
    // logging only - if non-zero timeout, then log success or warning(s))
    if (timeOut_ms > 0)
    {
        if (destroyedTimersCount >= timerIds.size())
        {
            UXAS_LOG_INFORM(s_typeName(), "::destroyTimers destroyed ", timerIds.size(), " timers within ", timeOut_ms, " ms timeout");
        }
        else
        {
            destroyedTimersCount = 0;
            for (auto itTimerId = timerIds.cbegin(), endItTimerId = timerIds.cend();
                    itTimerId != endItTimerId; itTimerId++)
            {
                if (disableOrDestroyTimerImpl(*itTimerId, true, 0))
                {
                    destroyedTimersCount++;
                }
                else
                {
                    auto itTimer = m_timersById.find(*itTimerId);
                    UXAS_LOG_WARN(s_typeName(), "::destroyTimers failed to destroy timer in set of ", timerIds.size(), " timers; timer ID ", *itTimerId, " with name ", itTimer->second.m_name, " within ", timeOut_ms, " ms timeout");
                }
            }
        }
    }
    return (destroyedTimersCount);
};

uint64_t
TimerManager::createTimerImpl(Timer&& timer)
{
    std::unique_lock<std::mutex> lock(m_mutex);
    timer.m_id = m_nextId++;
    m_timersById.emplace(timer.m_id, std::move(timer));
    return timer.m_id;
};

bool
TimerManager::startTimerImpl(uint64_t timerId, uint64_t startDelayFromNow_ms, uint64_t period_ms)
{
    std::unique_lock<std::mutex> lock(m_mutex);

    //
    // basic validation
    //
    if (timerId > (m_nextId - 1))
    {
        // Timer never existed
        UXAS_LOG_WARN(s_typeName(), "::startTimerImpl failed to start timer with non-existent timer ID ", timerId);
        return (false);
    }

    auto itTimer = m_timersById.find(timerId);
    if (itTimer == m_timersById.end())
    {
        // Timer was previously destroyed
        UXAS_LOG_WARN(s_typeName(), "::startTimerImpl failed to start destroyed timer ID ", timerId);
        return (false);
    }

    if (m_workerThread.get_id() == std::this_thread::get_id())
    {
        // recursive timer re-start on TimerManager's thread from within the callback is not supported
        UXAS_LOG_WARN(s_typeName(), "::startTimerImpl refused to re-start timer within the callback function "
                 "using the TimerManager's thread for timer ID ", timerId, " and name ", itTimer->second.m_name);
        return (false);
    }

    auto nowTime = std::chrono::system_clock::now();
    
    //
    // if timer is queued (already started), attempt dequeue
    //
    bool isQueued{false};
    auto queuedTimer = m_queue.find(std::ref(itTimer->second));
    if (queuedTimer != m_queue.end())
    {
        isQueued = true;
        UXAS_LOG_DEBUGGING(s_typeName(), "::startTimerImpl attempting to remove queued timer ID ", timerId);

        // calculate timer disable attempt timeout
        std::chrono::milliseconds reattemptSleep_ms = m_timeDurationReattempt_ms;
        int64_t tmOut_ms = std::chrono::duration_cast<std::chrono::milliseconds>(
                itTimer->second.m_nextCallbackTime - nowTime).count();
        if (tmOut_ms > 0) // queued for future callback
        {
            reattemptSleep_ms = std::chrono::milliseconds(1);
            tmOut_ms = 3 * m_timeDurationReattempt_ms.count();
        }
        else // in callback or post-callback
        {
            if (itTimer->second.m_period_ms.count() > 0 &&
                    itTimer->second.m_period_ms.count() < (3 * m_timeDurationReattempt_ms.count()))
            {
                // periodic timer with small period
                reattemptSleep_ms = std::chrono::milliseconds(1);
            }
            tmOut_ms = 10 * m_timeDurationReattempt_ms.count();
        }

        // iteratively attempt to disable (dequeue) timer (within timeout)
        while (isQueued)
        {
            if (disableOrDestroyExistingTimerImpl(timerId, *queuedTimer, false))
            {
                isQueued = false; // timer no longer queued
                UXAS_LOG_DEBUGGING(s_typeName(), "::startTimerImpl removed queued timer ID ", timerId);
            }
            else if (std::chrono::duration_cast<std::chrono::milliseconds>(
                    std::chrono::system_clock::now() - nowTime).count() > tmOut_ms)
            {
                UXAS_LOG_WARN(s_typeName(), "::startTimerImpl failed to disable and re-start timer ID ", timerId,
                         " and name ", itTimer->second.m_name, " within ", tmOut_ms, " ms timeout");
                break; // timed-out
            }
            else
            {
                // worker thread is performing callback - so wait, then re-attempt timer disable
                lock.unlock(); // allow other threads to request timer disable/destroy
                std::this_thread::sleep_for(reattemptSleep_ms);
                lock.lock();
            }
        }
    }

    //
    // if timer is not queued (not started), then start (queue) timer
    //
    if (!isQueued)
    {
        itTimer->second.m_nextCallbackTime = nowTime + std::chrono::milliseconds(startDelayFromNow_ms);
        itTimer->second.m_period_ms = std::chrono::milliseconds(period_ms);
        itTimer->second.m_isDisabled = false;
        itTimer->second.m_isToBeDestroyed = false;
        itTimer->second.m_isExecutingCallback = false;
        if (period_ms > 0)
        {
            UXAS_LOG_DEBUGGING(s_typeName(), "::startTimerImpl starting ", period_ms, " ms periodic timer ID ", timerId,
                       " with ms start time delay ", startDelayFromNow_ms);
        }
        else
        {
            UXAS_LOG_DEBUGGING(s_typeName(), "::startTimerImpl starting single-shot timer ID ", timerId,
                       " with ms start time delay ", startDelayFromNow_ms);
        }
        m_queue.insert(itTimer->second);
        m_wakeUp.notify_all();
        return (true);
    }
    else
    {
        UXAS_LOG_WARN(s_typeName(), "::startTimerImpl did not re-start timer ID ", timerId);
        return (false);
    }
};

bool
TimerManager::disableOrDestroyTimerImpl(uint64_t timerId, bool isDestroy, uint64_t timeOut_ms)
{
    bool isCompleted{false};
    if (timerId > (m_nextId - 1))
    {
        // Timer never existed
        UXAS_LOG_WARN(s_typeName(), "::disableOrDestroyTimerImpl failed to ", (isDestroy ? "destroy" : "disable"), " timer with invalid ID ", timerId);
        isCompleted = false;
    }
    else
    {
        auto itTimer = m_timersById.find(timerId);
        if (itTimer == m_timersById.end())
        {
            // Timer was previously destroyed
            if (!isDestroy)
            {
                UXAS_LOG_WARN(s_typeName(), "::disableOrDestroyTimerImpl failed to disable destroyed timer ID ", timerId);
            }
            isCompleted = true;
        }
        else
        {
            // Timer exists
            auto startTime = std::chrono::system_clock::now();
            while (true)
            {
                isCompleted = disableOrDestroyExistingTimerImpl(timerId, itTimer->second, isDestroy);
                if (isCompleted || timeOut_ms < 1)
                {
                    break;
                }
                else if (timeOut_ms > 0 &&
                        std::chrono::duration_cast<std::chrono::milliseconds>(
                        std::chrono::system_clock::now() - startTime).count() > static_cast<int64_t>(timeOut_ms))
                {
                    UXAS_LOG_WARN(s_typeName(), "::disableOrDestroyTimerImpl failed to ", (isDestroy ? "destroy" : "disable"),
                             " timer ID ", timerId, " and name ", itTimer->second.m_name,
                             " within ", timeOut_ms, " ms timeout");
                    break;
                }
                std::this_thread::sleep_for(m_timeDurationReattempt_ms);
            }
        }
    }

    m_wakeUp.notify_all();
    return (isCompleted);
};

bool
TimerManager::disableOrDestroyExistingTimerImpl(uint64_t timerId, Timer& timer, bool isDestroy)
{
    bool isCompleted{false};
    if (timer.m_isExecutingCallback)
    {
        // Timer is performing callback
        // so set disable/destroy flags
        // to be processed by worker thread
        // after completing callback
        timer.m_isDisabled = true;
        if (isDestroy)
        {
            timer.m_isToBeDestroyed = true;
        }
        UXAS_LOG_DEBUGGING(s_typeName(), "::disableOrDestroyExistingTimerImpl scheduled to ", (isDestroy ? "destroy" : "disable"), 
                   " timer (now performing callback) with ID ", timerId);
        isCompleted = false;
    }
    else
    {
        // remove Timer
        auto queuedTimer = m_queue.find(std::ref(timer));
        if (queuedTimer != m_queue.end())
        {
            m_queue.erase(std::ref(timer));
        }
        if (isDestroy)
        {
            m_timersById.erase(timerId);
        }
        UXAS_LOG_DEBUGGING(s_typeName(), "::disableOrDestroyExistingTimerImpl ", (isDestroy ? "destroyed" : "disabled"), " timer ID ", timerId);
        isCompleted = true;
    }

    return (isCompleted);
};

void
TimerManager::executeManagement()
{
    std::unique_lock<std::mutex> lock(m_mutex);

    while (!m_isFinished)
    {
        if (m_queue.empty())
        {
            // wait for creation and start of first Timer
            UXAS_LOG_DEBUGGING(s_typeName(), "::executeManagement waiting for creation and start of a timer");
            m_wakeUp.wait(lock);
        }
        else
        {
            // check Timer at front of queue
            auto firstTmr = m_queue.begin();
            Timer& timer = *firstTmr;
            auto now = std::chrono::system_clock::now();
            if (now >= timer.m_nextCallbackTime)
            {
                m_queue.erase(firstTmr);

                UXAS_LOG_DEBUGGING(s_typeName(), "::executeManagement invoking callback function for timer ID ", timer.m_id);
                timer.m_isExecutingCallback = true;
                lock.unlock(); // allow other threads to request Timer disable/destroy
                // invoke callback function
                timer.m_handler();
                lock.lock();
                timer.m_isExecutingCallback = false;
                UXAS_LOG_DEBUGGING(s_typeName(), "::executeManagement completed callback function invocation for timer ID ", timer.m_id);

                if (m_isFinished)
                {
                    UXAS_LOG_INFORM(s_typeName(), "::executeManagement finished - exiting main loop");
                    break;
                }
                else if (timer.m_isToBeDestroyed)
                {
                    // destroy was called for this Timer while performing callback 
                    // (this thread released the lock during the callback)
                    m_timersById.erase(timer.m_id);
                    UXAS_LOG_INFORM(s_typeName(), "::executeManagement destroyed timer ID ", timer.m_id);
                }
                else if (timer.m_isDisabled)
                {
                    UXAS_LOG_DEBUGGING(s_typeName(), "::executeManagement not invoking callback of disabled timer ID ", timer.m_id);
                }
                else
                {
                    if (timer.m_period_ms.count() > 0)
                    {
                        // re-schedule to callback m_period_ms milliseconds later
                        timer.m_nextCallbackTime = timer.m_nextCallbackTime + timer.m_period_ms;
                        m_queue.insert(timer);
                        UXAS_LOG_DEBUGGING(s_typeName(), "::executeManagement re-scheduled ", 
                                      timer.m_period_ms.count(), " ms periodic timer ID ", timer.m_id);
                    }
                    else
                    {
                        timer.m_isDisabled = true;
                        UXAS_LOG_DEBUGGING(s_typeName(), "::executeManagement disabled expired single-shot timer ID ", timer.m_id);
                    }
                }
            }
            else
            {
                // wait until the Timer is ready 
                // or for Timer creation/disable/destroy event notification
                m_wakeUp.wait_until(lock, timer.m_nextCallbackTime);
                UXAS_LOG_DEBUGGING(s_typeName(), "::executeManagement waiting to process a triggering event "
                        "or front-queued timer ID ", timer.m_id);
            }
        }
    }
};

}; //namespace common
}; //namespace uxas
