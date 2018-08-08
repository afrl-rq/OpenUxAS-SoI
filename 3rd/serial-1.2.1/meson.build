project('serial', 'cpp')

os = target_machine.system()
if os == 'linux'
  add_project_arguments('-DLINUX', language: ['c', 'cpp'])
endif

if meson.get_compiler('cpp').get_id() == 'msvc'
  cpp_args_serial = [
    '/std:c++14',
  ]
else
  cpp_args_serial = [
    '-std=c++11',
  ]
endif

lib = static_library(
  'serial',
  [
    'src/impl/unix.cc',
    'src/impl/win.cc',
    'src/serial.cc'
  ],
  cpp_args: cpp_args_serial,
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
