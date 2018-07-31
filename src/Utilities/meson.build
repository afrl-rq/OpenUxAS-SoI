srcs_utilities = [
  'Algebra.cpp',
  'CallbackTimer.cpp',
  'FileSystemUtilities.cpp',
  'Permute.cpp',
  'TimeUtilities.cpp',
  'FlatEarth.cpp',
  'RouteExtension.cpp',
  'SensorSteering.cpp',
  'UnitConversions.cpp',
  'UxAS_ConfigurationManager.cpp',
  'UxAS_ConsoleLogger.cpp',
  'UxAS_DatabaseLogger.cpp',
  'UxAS_DatabaseLoggerHelper.cpp',
  'UxAS_FileLogger.cpp',
  'UxAS_HeadLogDataDatabaseLogger.cpp',
  'UxAS_LogManager.cpp',
  'UxAS_SentinelSerialBuffer.cpp',
  'UxAS_Time.cpp',
  'UxAS_TimerManager.cpp',
  'UxAS_ZeroMQ.cpp',
]

incs_utilities = [
  include_directories(
    '../../src/Includes',
    '../../src/Plans',
  ),
  incs_lmcp,
]

if get_option('afrl_internal')
  incs_utilities += incs_utilities_internal
else
  srcs_utilities_internal = files()
endif

lib_utilities = static_library(
  'utilities',
  srcs_utilities,
  srcs_utilities_internal,
  dependencies: [
    dep_boost,
    dep_cppzmq,
    dep_pugixml,
    dep_sqlite3,
    dep_sqlitecpp,
    dep_zeromq,
  ],
  cpp_args: cpp_args,
  include_directories: incs_utilities,
)
