sub_gtest = subproject('gtest')

deps_test = deps

cpp_args_test = [
  '-std=c++11',
]

srcs_test = [
  sub_gtest.get_variable('libsources')
]

inc_test = [
  include_directories(
    'Test_Services',
    'Test_Utilities',
    '../src/Communications',
    '../src/Includes',
    '../src/LMCP',
    '../src/Services',
    '../src/Utilities',
    '../3rd/PugiXML/src',
    '../3rd/cppzmq-4.2.1',
    '../3rd/zeromq-4.1.1/include',
    '../3rd/sqlite-amalgamation-3120200',
    '../3rd/SQLiteCpp-1.3.1/include',
  ),
  sub_gtest.get_variable('incdir'),
]

libs_test = [
  lib_services,
  lib_tasks,
  lib_lmcp,
  lib_uxas_communications,
  lib_zeromq,
  lib_czmq,
  lib_utilities,
  lib_sqlitecpp,
  lib_sqlite3,
  lib_pugixml,
  lib_visilibity,
  lib_serial,
  lib_plans,
  lib_tinygps,
  lib_minizip,
  lib_zlib,
  lib_dpss,
]

if get_option('afrl_internal')
  inc_test += incs_internal
  libs_test += libs_internal
endif

link_args_test = link_args

subdir('Test_Services')
subdir('Test_Utilities')
