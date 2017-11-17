project('minizip', 'c')

lib = static_library('minizip', [
        'crypt.c'
	'ioapi.c',
	'ioapi_buf.c',
	'ioapi_mem.c',
	'unzip.c',
	'zip.c',
        'aes/aescrypt.c',
        'aes/aeskey.c',
        'aes/aes_ni.c',
        'aes/aestab.c',
        'aes/fileenc.c',
        'aes/hmac.c',
        'aes/prng.c',
        'aes/pwd2key.c',
        'aes/sha1.c',
	],
	c_args: [
        '-Wno-unused-parameter',
        '-Wno-unused-function',
        '-Wno-empty-body',
        '-Wno-sequence-point',
        '-D__USE_FILE_OFFSET64',
        '-D__USE_LARGEFILE64',
        '-D_LARGEFILE64_SOURCE',
        '-D_FILE_OFFSET_BIT=64',
        '-DHAVE_AES',
        '
	],
	include_directories: include_directories(
	        '../zlib-1.2.8',
                'aes',
	),
)
