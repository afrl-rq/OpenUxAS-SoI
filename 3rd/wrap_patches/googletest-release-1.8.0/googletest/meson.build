incdir = include_directories('include', '.')
libsources = files('src/gtest-all.cc')
mainsources = files('src/gtest_main.cc')

lib = static_library('gtest', libsources,
	dependencies: dependency('threads'),
	include_directories: include_directories(incdir),
)
