sub_gtest = subproject('gtest')

deps_test = deps

cpp_args_test = []
cpp_test = meson.get_compiler('cpp')

if cpp_test.get_id() == 'msvc'
  cpp_args_test += [
    '/std:c++14',
  ]
else
  cpp_args_test += [
    '-std=c++11',
    '-Wno-unused-function',
    '-Wno-unused-variable',
  ]
endif

inc_3rd = include_directories('.')
if get_option('internal_3rd_libraries')
  inc_3rd = include_directories(
      '../3rd/cppzmq-4.2.2',
      '../3rd/zeromq-4.2.3/include',
      '../3rd/zyre-2.0.0/include',
      '../3rd/sqlite-amalgamation-3120200',
      '../3rd/SQLiteCpp-1.3.1/include',
      '../3rd/googletest-release-1.8.0/googletest/include/',
    )
endif

srcs_test = [
]

inc_test = [
  include_directories(
    'Test_Services',
    'Test_Utilities',
    '../src/Utilities',
    '../src/Communications',
    '../src/Includes',
    '../src/Services',
    '../3rd/PugiXML/src',
  ),
  inc_3rd,
  incs_lmcp,
]

libs_test = [
  lib_services,
  lib_tasks,
  lib_lmcp,
  lib_uxas_communications,
  lib_utilities,
  lib_pugixml,
  lib_visilibity,
  lib_serial,
  lib_plans,
  lib_tinygps,
  lib_dpss,
  lib_daidalus,
]

if get_option('internal_3rd_libraries')
  libs_3rd = [  
    lib_gtest,
    lib_sqlitecpp,
    lib_sqlite3,
    lib_zeromq,
    lib_zyre,
    lib_czmq,
    lib_cppzmq,
    lib_minizip,
    lib_zlib,
  ]
  libs_test += libs_3rd
endif



if get_option('afrl_internal')
  inc_test += incs_internal
  libs_test += libs_internal
endif

link_args_test = link_args

subdir('Test_Services')
subdir('Test_Utilities')
