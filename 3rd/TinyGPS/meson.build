project('TinyGPS', 'cpp')

os = target_machine.system()
if os == 'linux'
  add_project_arguments('-DLINUX', language: ['c', 'cpp'])
endif

dep_boost = dependency('boost')

lib = static_library(
  'tinygps',
  [
    'TinyGPS.cpp',
  ],
  dependencies: [
    dep_boost,
  ],
  cpp_args: [
    '-std=c++11',
  ],
  include_directories: include_directories(
    '../../src/Includes',
    '../../src/Utilities',
  ),
)
