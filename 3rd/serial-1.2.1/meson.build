project('serial', 'cpp')

os = target_machine.system()
if os == 'linux'
  add_project_arguments('-DLINUX', language: ['c', 'cpp'])
endif

lib = static_library(
  'serial',
  [
    'src/impl/unix.cc',
    'src/impl/win.cc',
    'src/serial.cc'
  ],
  cpp_args: [
    '-std=c++11',
  ],
  include_directories: include_directories(
    'include',
  ),
)

dep = declare_dependency(
  link_with: lib,
  include_directories: include_directories(
    'include',
  ),
)
