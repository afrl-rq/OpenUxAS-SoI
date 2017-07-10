#ifndef _MADARA_LOGGER_DEFAULT_LOGGER_H_
#define _MADARA_LOGGER_DEFAULT_LOGGER_H_

#include <madara/logger/Logger.h>
#include <madara/logger/GlobalLogger.h>

/**
 * Fast version of the madara::Logger::log method, on default_logger. This
 * macro uses compiler optimizations to ensure that args are not
 * evaluated unless the level is appropriate for the loggers level.
* This makes logging transparent and minimally invasive, performance wise
 * @param  level   the logging level
 **/
#define madara_log(level, ...) \
          if (level <= ::madara::logger::global_logger->get_level ()) \
            ::madara::logger::global_logger->log (level, __VA_ARGS__);

#endif
