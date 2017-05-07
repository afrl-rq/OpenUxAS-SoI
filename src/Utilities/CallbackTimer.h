// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   CallbackTimer.h
 * Author: steve
 *
 * Created on February 10, 2014, 7:11 PM
 */

#ifndef CALLBACKTIMER_H
#define CALLBACKTIMER_H

#include <thread>
#include <mutex>

#include <functional>

#include "TypeDefs/UxAS_TypeDefs_Thread.h"
//#include "TypeDefs/UxAS_TypeDefs_ZeroMQ.h"


namespace uxas
{
namespace common
{
namespace utilities
{

/*! \class c_CallbackTimer
     * \brief Implements a timer function that runs in its own thread and calls a
     * <I>callback function</I>, provided by the calling class, when the timer
     * expires, or is canceled.

     * 
     * 
     * @par Highlights:
     * <ul style="padding-left:1em;margin-left:0">
     * <li> <B>Timer Initialization/Operation</B> - 
     * After an instance of the @ref c_CallbackTimer class is created, the function,
     * @ref StartCallbackTimer is called  to initialize and start the timer.
     * @ref StartCallbackTimer takes an expiration time, and a callback function
     * as inputs. The callback function must accept a @ref c_CallbackTimer::enReturnValue
     * argument, and return a <I>void</I>. NOTE 1: the callback function will be called from
     * the timer thead, therefore memory access must be syncronized, e.g. mutex.
     * NOTE 2: the following syntax is used to
     * specifiy the callback function:
     * 
     * <I>std::bind(&Your_Class::CallBackName,this, std::placeholders::_1)</I>
     * 
     * or in the @ref StartCallbackTimer function call:
     * 
     *StartCallbackTimer(ui32ExpirationTime_ms,std::bind(&Your_Class::CallBackName,this, std::placeholders::_1)) 
     * 
     * <li> <B>Expiration Time Reset</B> - 
     * While the timer is operating, calling the function @ref ResetTime() will
     * add the given amount of time to the expiration timer.
     * 
     * <li> <B>Timer Cancellation</B> - 
     * While the timer is operating, calling the function @ref CancelTimer() will cause 
     * the timer to expire immediately. The <I>callback</I> will be called with
     * the value: @ref c_CallbackTimer::retCancel.
     * 
     * <li> <B>Timer Restart</B> - 
     * While the timer is operating, calling the function @ref StartCallbackTimer(...)
     * will cause the timer to expire immediately. The original <I>callback</I> 
     * will be called with the value: @ref c_CallbackTimer::retCancel. The expiration
     * time and callback function arguments in @ref StartCallbackTimer(...) will
     * then be used to restart the timer.
     * 
     * </ul>
     */


    class c_CallbackTimer
    {
    public:

        enum enTimerCommands
        {
            commandNone,
            commandKillTimer,
            commandCancelTimer,
            commandTimeReset,
            commandTimeExtend
        };

        enum enReturnValue
        {
            retNormal,
            retCancel,
            retErrorConvertingTime
        };

        enum enTimerType
        {
            tmrtypSingle,
            tmrtypPeriodic
        };
    public:
        c_CallbackTimer(const enTimerType& tmrtypType = tmrtypSingle);
        virtual ~c_CallbackTimer();

    private:
        c_CallbackTimer(const c_CallbackTimer& orig) = delete; //no copying
        c_CallbackTimer& operator=(const c_CallbackTimer&) = delete; //no copying

    public:
        /*! @name Public Member Functions
         *   
         */
        ///@{
        //! 
        /*! \brief this function initializes/reinitializes the timer thread and 
         * starts the timer
         * @param ui32ExpirationTime_ms is the expiration time duration in milliseconds.
         * @param callbackFunction is the function that is called when the timer
         * is canceled or the timer expires. */
        void StartCallbackTimer(const int64_t& ui32ExpirationTime_ms, std::function<void(enReturnValue) > callbackFunction);
        /*! \brief this function resets the timer to the existing time period. */
        void ResetTime();
        /*! \brief this function extends the current expiration time from the 
         * current time to extendedTime_ms. If the current expiration time is 
         * greater than the extended time, this this function has no effect.
         * @param extendedTime_ms is the time extension time duration in milliseconds. */
        void ExtendTime(const uint32_t& extendedTime_ms);
        /*! \brief this function causes 
         * the timer to expire immediately. The <I>callback</I> will be called with
         * the value: @ref c_CallbackTimer::retCancel. */
        void CancelTimer();
        /*! \brief this function causes the timer to expire immediately. The 
         * <I>callback</I> will not be called. */
        void KillTimer();
        ///@}


    protected:
        /*! @name Protected Member Functions
         *   
         */
        ///@{
        //! 
        /*! \brief this function is the timer thread
         * @param ui32ExpirationTime_ms is the expiration time duration in milliseconds.
         * @param callbackFunction is the function that is called when the timer
         * is canceled or the timer expires. */
        void CallbackTimerExecutitve(const int64_t& time_ms, std::function<void(enReturnValue) > callbackFunction);
        ///@}


    public:


    protected:
        /*! @name Protected accessor Functions
         *   
         */
        ///@{
        //! 

        /*! \brief thread safe accessor function for: bool m_bThreadRunning */
        bool get_isThreadRunning() {
            std::lock_guard<std::mutex> lock(_mutexThreadRunning);
            return (_isThreadRunning);
        };

        /*! \brief thread safe accessor function for: bool m_bThreadRunning */
        void set_isThreadRunning(const bool& isThreadRunning) {
            std::lock_guard<std::mutex> lock(_mutexThreadRunning);
            _isThreadRunning = isThreadRunning;
        };

        /*! \brief thread safe accessor function for: bool m_bThreadRunning */
        enTimerCommands get_currentCommand() {
            std::lock_guard<std::mutex> lock(_mutexCurrentCommand);
            return (_currentCommand);
        };

        /*! \brief thread safe accessor function for: bool m_bThreadRunning */
        void set_currentCommand(const enTimerCommands& commandCurrent) {
            std::lock_guard<std::mutex> lock(_mutexCurrentCommand);
            _currentCommand = commandCurrent;
        };

        /*! \brief thread safe accessor function for: bool m_bThreadRunning */
        int64_t get_commandArgument_1() {
            std::lock_guard<std::mutex> lock(_mutexCommandArgument_1);
            return (_commandArgument_1);
        };

        /*! \brief thread safe accessor function for: bool m_bThreadRunning */
        void set_commandArgument_1(const int64_t& commandArgument_1) {
            std::lock_guard<std::mutex> lock(_mutexCommandArgument_1);
            _commandArgument_1 = commandArgument_1;
        };

        ///@}

    protected:

        /*! \brief Pointer to the component's thread.  */
        n_Typedefs::PTR_THREAD_t _thrThread;

        /*! \brief  synchronize low level operations*/
        std::mutex _mutexThreadRunning;
        /*! \brief  this flag is set to true when the thread is running. */
        bool _isThreadRunning = {false};
        
        /*! \brief  synchronize low level operations*/
        std::mutex _mutexCurrentCommand;
        enTimerCommands _currentCommand = {commandNone};
        
        std::mutex _mutexCommandArgument_1;
        int64_t _commandArgument_1 = {0};
        
        /*! \brief  type of timer, e.g. single, periodic*/
        enTimerType _tmrtypTimerType = {tmrtypSingle};


    private:

    };

}       //namespace utilities
}       //namespace common
}       //namespace uxas

#endif /* CALLBACKTIMER_H */

