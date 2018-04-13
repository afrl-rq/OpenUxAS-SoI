incdir = include_directories('include', '.')
libsources = files('src/gtest-all.cc')
mainsources = files('src/gtest_main.cc')

lib = static_library(
  'gtest',
  libsources,
  dependencies: dependency('threads'),
  include_directories: incdir,
)

dep = declare_dependency(
  link_with: lib,
  include_directories: incdir,
)
