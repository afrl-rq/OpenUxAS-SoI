srcs_utilities = [
  'Algebra.cpp',
  'CallbackTimer.cpp',
  'FileSystemUtilities.cpp',
  'Permute.cpp',
  'TimeUtilities.cpp',
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
]

incs_utilities = [
  include_directories(
    '../../src/Includes',
    '../../3rd/PugiXML/src',
    '../../sqlite-amalgamation-3120200',
    '../../SQLiteCpp-1.3.1/include',
  ),
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
  ],
  cpp_args: [
    '-std=c++11',
    '-Wno-unused-function',
    '-Wno-unused-variable',
  ],
  include_directories: incs_utilities,
)
