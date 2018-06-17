dep_gtest = dependency(
  'gtest',
  fallback: ['gtest', 'dep']
)

deps_test = deps + [
  dep_gtest
]

cpp_args_test = cpp_args

inc_test = [
  include_directories(
    'Test_Services',
    'Test_Utilities',
    'Test_Units',
    '../src/Utilities',
    '../src/Communications',
    '../src/Includes',
    '../src/Services',
    '../src/VisilibityLib',
  ),
  incs_lmcp,
]


libs_test = libs
link_args_test = link_args

subdir('Test_Services')
subdir('Test_Utilities')
subdir('Test_Units')

