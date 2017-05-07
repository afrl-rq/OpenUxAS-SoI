// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#ifndef UXAS_COMMON_LOG_LOG_SEVERITY_LEVEL_H
#define UXAS_COMMON_LOG_LOG_SEVERITY_LEVEL_H

#include <string>

namespace uxas
{
namespace common
{
namespace log
{

/** \class LogSeverityLevel
 * (enum LogSeverityLevel)
 * 
 * \par Description:
 * 
 * \n
 */
enum class LogSeverityLevel
{// ordered by *severity* level
    UXASDEBUG = 1,
    UXASINFO,
    UXASWARNING,
    UXASERROR
};

class LogSeverityLevelString
{// ordered by *severity* level
public:
    static const std::string& LOGDEBUG() { static std::string s_string("DEBUG"); return(s_string); };
    static const std::string& LOGINFO() { static std::string s_string("INFO"); return(s_string); };
    static const std::string& LOGWARN() { static std::string s_string("WARN"); return(s_string); };
    static const std::string& LOGERROR() { static std::string s_string("ERROR"); return(s_string); };
};

}; //namespace log
}; //namespace common
}; //namespace uxas

#endif /* UXAS_COMMON_LOG_LOG_SEVERITY_LEVEL_H */
