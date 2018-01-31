deps_test = deps + [
  subproject('gtest').get_variable('gtest_dep'),
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

inc_test = [
  include_directories(
    'Test_Services',
    'Test_Utilities',
    '../src/Utilities',
    '../src/Communications',
    '../src/Includes',
    '../src/Services',
  ),
  incs_lmcp,
]

libs_test = libs
link_args_test = link_args

subdir('Test_Services')
subdir('Test_Utilities')
