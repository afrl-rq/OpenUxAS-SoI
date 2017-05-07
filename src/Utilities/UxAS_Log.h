// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#ifndef UXAS_COMMON_LOG_LOG_H
#define UXAS_COMMON_LOG_LOG_H

#include "UxAS_LogManager.h"

//#define DEBUG_VERBOSE_LOGGING_ENABLED_BRIDGE
//#define DEBUG_VERBOSE_LOGGING_ENABLED_CCA
//#define DEBUG_VERBOSE_LOGGING_ENABLED_KESTREL
//#define DEBUG_VERBOSE_LOGGING_ENABLED_MESSAGING
//#define DEBUG_VERBOSE_LOGGING_ENABLED_TESTFRAMEWORK
//#define DEBUG_VERBOSE_LOGGING_ENABLED_TIME

//#define DEBUG_VERBOSE_LOGGING_ENABLED
//#define DEBUG_LOGGING_ENABLED
//#define INFO_LOGGING_ENABLED
#define WARN_LOGGING_ENABLED
#define ERROR_LOGGING_ENABLED

#define INFO_LOGGING_FUNCTIONAL_TEST
#ifdef INFO_LOGGING_FUNCTIONAL_TEST
/** \brief Log information message consisting of one-many arguments.  
 * Arguments can be of type string, integer, double or an expression 
 * (e.g., totalCount + loopCount).  Recommended first argument is 
 * class and function name (e.g., ServiceBase::initialize).
 */
#define LOG_INFORM_FUNCTIONAL_TEST uxas::common::log::LogManager::getInstance().log<uxas::common::log::LogSeverityLevel::UXASINFO>
#else
/** \brief Log information message function disabled.
 */
#define LOG_INFORM_FUNCTIONAL_TEST(...)
#endif

#define INFO_LOGGING_ASSIGNMENT
#ifdef INFO_LOGGING_ASSIGNMENT
/** \brief Log information message consisting of one-many arguments.  
 * Arguments can be of type string, integer, double or an expression 
 * (e.g., totalCount + loopCount).  Recommended first argument is 
 * class and function name (e.g., ServiceBase::initialize).
 */
#define LOG_INFORM_ASSIGNMENT uxas::common::log::LogManager::getInstance().log<uxas::common::log::LogSeverityLevel::UXASINFO>
#else
/** \brief Log information message function disabled.
 */
#define LOG_INFORM_ASSIGNMENT(...)
#endif



#ifdef DEBUG_VERBOSE_LOGGING_ENABLED_BRIDGE
/** \brief Log highly-detailed debug message consisting of one-many arguments.  
 * Arguments can be of type string, integer, double or an expression 
 * (e.g., totalCount + loopCount).  Recommended first argument is 
 * class and function name (e.g., ServiceBase::initialize).
 */
#define LOG_DEBUG_VERBOSE_BRIDGE uxas::common::log::LogManager::getInstance().log<uxas::common::log::LogSeverityLevel::UXASDEBUG>
#else
/** \brief Log debug details message function disabled.
 */
#define LOG_DEBUG_VERBOSE_BRIDGE(...)
#endif

#ifdef DEBUG_VERBOSE_LOGGING_ENABLED_CCA
/** \brief Log highly-detailed debug message consisting of one-many arguments.  
 * Arguments can be of type string, integer, double or an expression 
 * (e.g., totalCount + loopCount).  Recommended first argument is 
 * class and function name (e.g., ServiceBase::initialize).
 */
#define LOG_DEBUG_VERBOSE_CCA uxas::common::log::LogManager::getInstance().log<uxas::common::log::LogSeverityLevel::UXASDEBUG>
#else
/** \brief Log debug details message function disabled.
 */
#define LOG_DEBUG_VERBOSE_CCA(...)
#endif

#ifdef DEBUG_VERBOSE_LOGGING_ENABLED_KESTREL
/** \brief Log highly-detailed debug message consisting of one-many arguments.  
 * Arguments can be of type string, integer, double or an expression 
 * (e.g., totalCount + loopCount).  Recommended first argument is 
 * class and function name (e.g., ServiceBase::initialize).
 */
#define LOG_DEBUG_VERBOSE_KESTREL uxas::common::log::LogManager::getInstance().log<uxas::common::log::LogSeverityLevel::UXASDEBUG>
#else
/** \brief Log debug details message function disabled.
 */
#define LOG_DEBUG_VERBOSE_KESTREL(...)
#endif

#ifdef DEBUG_VERBOSE_LOGGING_ENABLED_MESSAGING
/** \brief Log highly-detailed debug message consisting of one-many arguments.  
 * Arguments can be of type string, integer, double or an expression 
 * (e.g., totalCount + loopCount).  Recommended first argument is 
 * class and function name (e.g., ServiceBase::initialize).
 */
#define LOG_DEBUG_VERBOSE_MESSAGING uxas::common::log::LogManager::getInstance().log<uxas::common::log::LogSeverityLevel::UXASDEBUG>
#else
/** \brief Log debug details message function disabled.
 */
#define LOG_DEBUG_VERBOSE_MESSAGING(...)
#endif

#ifdef DEBUG_VERBOSE_LOGGING_ENABLED_TESTFRAMEWORK
/** \brief Log highly-detailed debug message consisting of one-many arguments.  
 * Arguments can be of type string, integer, double or an expression 
 * (e.g., totalCount + loopCount).  Recommended first argument is 
 * class and function name (e.g., ServiceBase::initialize).
 */
#define LOG_DEBUG_VERBOSE_TESTFRAMEWORK uxas::common::log::LogManager::getInstance().log<uxas::common::log::LogSeverityLevel::UXASDEBUG>
#else
/** \brief Log debug details message function disabled.
 */
#define LOG_DEBUG_VERBOSE_TESTFRAMEWORK(...)
#endif

#ifdef DEBUG_VERBOSE_LOGGING_ENABLED_TIME
/** \brief Log highly-detailed debug message consisting of one-many arguments.  
 * Arguments can be of type string, integer, double or an expression 
 * (e.g., totalCount + loopCount).  Recommended first argument is 
 * class and function name (e.g., ServiceBase::initialize).
 */
#define LOG_DEBUG_VERBOSE_TIME uxas::common::log::LogManager::getInstance().log<uxas::common::log::LogSeverityLevel::UXASDEBUG>
#else
/** \brief Log debug details message function disabled.
 */
#define LOG_DEBUG_VERBOSE_TIME(...)
#endif

#ifdef DEBUG_VERBOSE_LOGGING_ENABLED
/** \brief Log highly-detailed debug message consisting of one-many arguments.  
 * Arguments can be of type string, integer, double or an expression 
 * (e.g., totalCount + loopCount).  Recommended first argument is 
 * class and function name (e.g., ServiceBase::initialize).
 */
#define LOG_DEBUG_VERBOSE uxas::common::log::LogManager::getInstance().log<uxas::common::log::LogSeverityLevel::UXASDEBUG>
#else
/** \brief Log debug details message function disabled.
 */
#define LOG_DEBUG_VERBOSE(...)
#endif
        
#ifdef DEBUG_LOGGING_ENABLED
/** \brief Log debug message consisting of one-many arguments.  
 * Arguments can be of type string, integer, double or an expression 
 * (e.g., totalCount + loopCount).  Recommended first argument is 
 * class and function name (e.g., ServiceBase::initialize).
 */
#define LOG_DEBUGGING uxas::common::log::LogManager::getInstance().log<uxas::common::log::LogSeverityLevel::UXASDEBUG>
#else
/** \brief Log debug message function disabled.
 */
#define LOG_DEBUGGING(...)
#endif

#ifdef INFO_LOGGING_ENABLED
/** \brief Log information message consisting of one-many arguments.  
 * Arguments can be of type string, integer, double or an expression 
 * (e.g., totalCount + loopCount).  Recommended first argument is 
 * class and function name (e.g., ServiceBase::initialize).
 */
#define LOG_INFORM uxas::common::log::LogManager::getInstance().log<uxas::common::log::LogSeverityLevel::UXASINFO>
#else
/** \brief Log information message function disabled.
 */
#define LOG_INFORM(...)
#endif

#ifdef WARN_LOGGING_ENABLED
/** \brief Log warning message consisting of one-many arguments.  
 * Arguments can be of type string, integer, double or an expression 
 * (e.g., totalCount + loopCount).  Recommended first argument is 
 * class and function name (e.g., ServiceBase::initialize).
 */
#define LOG_WARN uxas::common::log::LogManager::getInstance().log<uxas::common::log::LogSeverityLevel::UXASWARNING>
#else
/** \brief Log warning message function disabled.
 */
#define LOG_WARN(...)
#endif

#ifdef ERROR_LOGGING_ENABLED
/** \brief Log error message consisting of one-many arguments.  
 * Arguments can be of type string, integer, double or an expression 
 * (e.g., totalCount + loopCount).  Recommended first argument is 
 * class and function name (e.g., ServiceBase::initialize).
 */
#define LOG_ERROR uxas::common::log::LogManager::getInstance().log<uxas::common::log::LogSeverityLevel::UXASERROR>
#else
/** \brief Log error message function disabled.
 */
#define LOG_ERROR(...)
#endif

#endif	/* UXAS_COMMON_LOG_LOG_H */
