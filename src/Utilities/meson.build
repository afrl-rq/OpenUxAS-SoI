srcs_utilities = [
  'Algebra.cpp',
  'CallbackTimer.cpp',
  'DubinsUtilities.cpp',
  'FileSystemUtilities.cpp',
  'Permute.cpp',
  'TimeUtilities.cpp',
  'FlatEarth.cpp',
  'RouteExtension.cpp',
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
  ),
  incs_lmcp,
]

if get_option('afrl_internal')
  incs_utilities += incs_utilities_internal
else
  srcs_utilities_internal = files()
endif

cpp_args_utilities = cpp_args

if cpp.get_id() == 'msvc'
  cpp_args_utilities += [
    '-DZMQ_STATIC',
    '-DCZMQ_STATIC',
    '-DZYRE_STATIC',
    '-DLIBZMQ_STATIC',
    '-DLIBCZMQ_STATIC',
    '-DLIBZYRE_STATIC',
  ]
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
  cpp_args: cpp_args_utilities,
  include_directories: incs_utilities,
)
