cpp_args = []
cpp = meson.get_compiler('cpp')

if cpp.get_id() != 'msvc'
  cpp_args += [
    '-std=c++11',
    '-Wno-unused-function',
    '-Wno-unused-variable',
  ]
endif

lib_visilibity = static_library(
  'visilibity',
  [
    'visilibity.cpp',
  ],
  cpp_args: cpp_args,
)
