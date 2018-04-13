project('sqlite3', 'c')

lib = static_library(
  'sqlite3',
  'sqlite3.c',
)

dep = declare_dependency(
  link_with: lib,
  include_directories: include_directories(
    '.',
  ),
)
