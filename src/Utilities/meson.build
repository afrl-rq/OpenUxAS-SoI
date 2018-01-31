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
  'UxAS_ZeroMQ.cpp',
]

inc_3rd = include_directories('.')
if get_option('internal_3rd_libraries')
  inc_3rd = include_directories(
    )
endif

incs_utilities = [
  include_directories(
    '../../src/Includes',
  ),
  inc_3rd,
]

if get_option('afrl_internal')
  incs_utilities += incs_utilities_internal
else
  srcs_utilities_internal = files()
endif

cpp_args = []

cpp = meson.get_compiler('cpp')
if cpp.get_id() == 'msvc'
  cpp_args += [
    '/std:c++14',
    '-DZMQ_STATIC',
    '-DCZMQ_STATIC',
    '-DZYRE_STATIC',
    '-DLIBZMQ_STATIC',
    '-DLIBCZMQ_STATIC',
    '-DLIBZYRE_STATIC',
  ]
else
  cpp_args += [
    '-std=c++11',
    '-Wno-unused-function',
    '-Wno-unused-variable',
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
  cpp_args: cpp_args,
  include_directories: incs_utilities,
)
