import struct


def bytes_as_str(msg):
    """Return a string representing a series of bytes."""
    print(" ".join(["%02X" % ord(c) for c in msg]))


class Buffer(object):

    SUPPORTED_TYPES = set(['int32', 'int64',
                           'uint16', 'uint32',
                           'real32', 'real64',
                           'byte', 'bool',
                           'string'])

    BASIC_TYPES = {
        'int32': '>i',
        'int64': '>q',
        'uint16': '>H',
        'uint32': '>I',
        'real32': '>f',
        'real64': '>d',
        'byte': '>B',
        'bool': '>?'}

    def __init__(self, data=''):
        self.data = data
        self.pos = 0

    def unpack_struct(self, fmt):
        result = struct.unpack_from(fmt, self.data, self.pos)
        self.pos += struct.calcsize(fmt)
        return result

    def unpack(self, type_name):
        assert type_name in self.SUPPORTED_TYPES, \
            'unknown type: %s' % type_name
        if type_name in self.BASIC_TYPES:
            value = self.unpack_struct(self.BASIC_TYPES[type_name])[0]
        elif type_name == 'string':
            string_size = self.unpack('uint16')
            value = self.unpack_struct('%ss' % string_size)[0]

        return value
