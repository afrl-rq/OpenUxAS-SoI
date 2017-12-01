project('minizip', 'c')

minizip_src = [
        'crypt.c',
	'ioapi.c',
	'ioapi_buf.c',
	'ioapi_mem.c',
	'unzip.c',
	'zip.c',
]

c_args = []

os = target_machine.system()
if os == 'windows'
   minizip_src += 'iowin32.c'
   c_args += '-D_CRT_SECURE_NO_DEPRECATE'
else
   c_args += [
	'-D__USE_FILE_OFFSET64',
	'-D__USE_LARGEFILE64',
	'-D_LARGEFILE64_SOURCE',
	'-D_FILE_OFFSET_BIT=64',
]
endif

lib = static_library('minizip',
        minizip_src,
	c_args: c_args,
	include_directories: include_directories(
	        '../zlib-1.2.8',
	),
)
