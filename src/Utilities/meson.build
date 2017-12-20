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

incs_utilities = [
  include_directories(
    '../../src/Includes',
    '../../3rd/cppzmq-4.2.2',
    '../../3rd/PugiXML/src',
    '../../3rd/sqlite-amalgamation-3120200',
    '../../3rd/SQLiteCpp-1.3.1/include',
    '../../3rd/zeromq-4.2.3/include',
  ),
]

deps_utilities = [
    dep_boost,
]

if get_option('afrl_internal')
  incs_utilities += incs_utilities_internal
  deps_utilities += deps_utilities_internal
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
  dependencies: deps_utilities,
  cpp_args: cpp_args,
  include_directories: incs_utilities,
)
