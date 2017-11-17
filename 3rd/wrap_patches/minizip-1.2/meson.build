project('minizip', 'c')

lib = static_library('minizip', [
	'crypt.c',
	'ioapi.c',
	'ioapi_buf.c',
	'ioapi_mem.c',
	'miniunz.c',
	'minizip.c',
	'unzip.c',
	'zip.c',
	],
	c_args: [
	],
	include_directories: include_directories(
	        '../zlib-1.2.8'
	),
)

