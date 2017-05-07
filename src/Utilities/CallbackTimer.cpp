// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   CallbackTimer.cpp
 * Author: steve
 * 
 * Created on February 10, 2014, 7:11 PM
 */

#include "CallbackTimer.h"


#include "TimeUtilities.h"    //_oneHundredMicroseconds


#include <iostream>     // std::cout, cerr, etc
#include <chrono>       // time functions

#define COUT_FILE_LINE_MSG(MESSAGE) std::cout << "c_CallbackTimer:: " << __FILE__ << ":" << __LINE__ << ":" << MESSAGE << std::endl;std::cout.flush();
#define CERR_FILE_LINE_MSG(MESSAGE) std::cerr << "c_CallbackTimer:: " << __FILE__ << ":" << __LINE__ << ":" << MESSAGE << std::endl;std::cerr.flush();


namespace uxas
{
namespace common
{
namespace utilities
{

    
    c_CallbackTimer::c_CallbackTimer(const enTimerType& tmrtypType)
    :_tmrtypTimerType(tmrtypType)        
    {
        int64_t temp = {0};
    }

    c_CallbackTimer::~c_CallbackTimer()
    {
        KillTimer();  // need to get the thread to stop itself
        if (_thrThread)
        {
            if (_thrThread->joinable())
            {
                _thrThread->join();
            }
        }
    }

    void c_CallbackTimer::ResetTime()
    {
        if (get_isThreadRunning())
        {
            set_currentCommand(commandTimeReset);
        }
    };

    void c_CallbackTimer::ExtendTime(const uint32_t& extendedTime_ms)
    {
        if (get_isThreadRunning())
        {
            set_commandArgument_1(extendedTime_ms);
            set_currentCommand(commandTimeExtend);
        }
    };

    void c_CallbackTimer::CancelTimer()
    {
        if (get_isThreadRunning())
        {
            set_currentCommand(commandCancelTimer);
        }
    };

    void c_CallbackTimer::KillTimer()
    {
       if (get_isThreadRunning())
        {
            set_currentCommand(commandKillTimer);
        }
    };

    void c_CallbackTimer::StartCallbackTimer(const int64_t& time_ms, std::function<void(c_CallbackTimer::enReturnValue) > callbackFunction)
    {
        if(get_isThreadRunning())
        {
            ExtendTime(time_ms);
        }
        else
        {
            KillTimer();  // need to get the thread to stop itself
            if (_thrThread)
            {
                if (_thrThread->joinable())
                {
                    _thrThread->join();
                }
            }
            set_isThreadRunning(true);
            _thrThread.reset(new std::thread(&c_CallbackTimer::CallbackTimerExecutitve, this, time_ms, callbackFunction));
        }
    }

    void c_CallbackTimer::CallbackTimerExecutitve(const int64_t& time_ms, std::function<void(enReturnValue) > callbackFunction)
    {
        std::chrono::milliseconds timeOut_msec(time_ms);
        auto start = std::chrono::high_resolution_clock::now();

        while (get_isThreadRunning())
        {
            auto timeElapsed_msec = std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::high_resolution_clock::now() - start);
            if (timeElapsed_msec < timeOut_msec)
            {
                switch (get_currentCommand())
                {
                    default:
                    case commandNone:
                        break;
                    case commandKillTimer:
                        set_isThreadRunning(false);
                        COUT_FILE_LINE_MSG("")
                        set_currentCommand(commandNone);
                        break;
                    case commandCancelTimer:
                        callbackFunction(retCancel);
                        set_isThreadRunning(false);
                        COUT_FILE_LINE_MSG("")
                        set_currentCommand(commandNone);
                        break;
                    case commandTimeReset:
                        start = std::chrono::high_resolution_clock::now();
                        COUT_FILE_LINE_MSG("")
                        set_currentCommand(commandNone);
                        break;
                    case commandTimeExtend:
                        std::chrono::milliseconds timeExtend_msec(get_commandArgument_1());
                        std::chrono::milliseconds timeOutremaining_msec = timeOut_msec - timeElapsed_msec;
                        if(timeExtend_msec > timeOutremaining_msec)
                        {
                            start = std::chrono::high_resolution_clock::now();
                            timeOut_msec = timeExtend_msec;
                        }
                        COUT_FILE_LINE_MSG("Time Extended to " << timeExtend_msec.count() << "ms from now.")
                        set_currentCommand(commandNone);
                        set_commandArgument_1(0);
                        break;
                }
            }
            else
            {
                callbackFunction(retNormal);
                if(_tmrtypTimerType == tmrtypPeriodic)
                {
                    // restart time
                    start = std::chrono::high_resolution_clock::now();
                }
                else
                {
                    set_isThreadRunning(false);
                }
            }
            //std::this_thread::yield();
            std::this_thread::sleep_for(uxas::common::utilities::c_TimeUtilities::_oneHundredMicroseconds);
        } //while (1)
    }
    
}       //namespace utilities
}       //namespace common
}       //namespace uxas


