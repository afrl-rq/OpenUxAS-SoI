project('zlib', 'c')

lib = static_library(
  'zlib',
  [
    'adler32.c',
    'compress.c',
    'crc32.c',
    'deflate.c',
    'gzclose.c',
    'gzlib.c',
    'gzread.c',
    'gzwrite.c',
    'infback.c',
    'inffast.c',
    'inflate.c',
    'inftrees.c',
    'trees.c',
    'uncompr.c',
    'zutil.c',
  ],
)

dep = declare_dependency(
  link_with: lib,
  include_directories: include_directories(
    '.',
  ),
)
