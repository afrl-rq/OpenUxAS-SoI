sub_gtest = subproject('gtest')

deps_test = deps + [
  sub_gtest.get_variable('gtest_dep'),
]

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
  lib_visilibity,
  lib_plans,
  lib_dpss,
]

if get_option('internal_3rd_libraries')
  libs_3rd = [
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
