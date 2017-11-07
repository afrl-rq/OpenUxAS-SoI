project('minizip', 'c')

lib = static_library(
  'minizip',
  [
    'ioapi.c',
    'ioapi_buf.c',
    'ioapi_mem.c',
    'miniunz.c',
    'minizip.c',
    'unzip.c',
    'zip.c',
  ],
  c_args: [
    '-DNOCRYPT',
    '-DNOUNCRYPT',
  ],
  include_directories: include_directories(
    '../zlib-1.2.8'
  ),
)
