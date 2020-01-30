import re
import random
import struct
from pylmcp.model.enum import EnumModel


class ObjectAttr(object):

    BASIC_TYPES = {
        'int32': {'rep': '>i'},
        'int64': {'rep': '>q'},
        'uint16': {'rep': '>H'},
        'uint32': {'rep': '>I'},
        'bool': {'rep': '>?'},
        'string': {'rep': None},  # ????
        'real32': {'rep': '>f'},
        'real64': {'rep': '>d'},
        'byte': {'rep': '>B'}}

    def __init__(self,
                 attr_type,
                 name,
                 units,
                 min_array_length,
                 max_array_length,
                 is_large_array,
                 optional,
                 object_class,
                 model_db):
        self.object_class = object_class
        self.model_db = model_db
        self.attr_type = attr_type
        self.name = name
        self.unit = units
        self.optional = optional

        self.is_large_array = is_large_array
        self.max_array_length = max_array_length
        self.min_array_length = min_array_length

        self.is_array = self.min_array_length is not None
        self.is_static_array = \
            self.max_array_length == self.min_array_length

    def pack(self, value):
        def pack_simple_value(type_name, value):
            result = b''
            if type_name in self.BASIC_TYPES:
                if self.BASIC_TYPES[type_name]['rep'] is not None:
                    result = struct.pack(
                        self.BASIC_TYPES[type_name]['rep'], value)
                elif type_name == 'string':
                    result += struct.pack('>H', len(value))
                    result += struct.pack('%ss' % len(value), value.encode('utf-8'))
            else:
                model = self.model_db.types[type_name]
                if isinstance(model, EnumModel):
                    result = struct.pack(">i", value)
                else:
                    result += struct.pack("B", value is not None)
                    if value is not None:
                        result += model.pack(value, include_headers=False)
            return result

        if self.is_array:
            result = b''
            if not self.is_static_array:
                if self.is_large_array:
                    result += struct.pack('>I', len(value))
                else:
                    result += struct.pack('>H', len(value))
            for el in value:
                result += pack_simple_value(self.attr_type, el)
        else:
            result = pack_simple_value(self.attr_type, value)
        return result

    def random_value(self):

        def random_simple_value(type_name):
            if type_name == 'byte':
                return random.randint(0, 255)
            elif type_name == 'int32':
                return random.randint(-2 ** 31, 2 ** 31 - 1)
            elif type_name == 'int64':
                return random.randint(-2 ** 63, 2 ** 63 - 1)
            elif type_name == 'uint16':
                return random.randint(0, 2 ** 16 - 1)
            elif type_name == 'uint32':
                return random.randint(0, 2 ** 31 - 1)
            elif type_name == 'bool':
                return {0: False, 1: True}[random.randint(0, 1)]
            elif type_name == 'string':
                return "Hello"
            elif type_name == 'real32':
                return struct.unpack_from(
                    '>f',
                    struct.pack('>f', random.random()))[0]
            elif type_name == 'real64':
                return struct.unpack_from(
                    '>d',
                    struct.pack('>d', random.random()))[0]

            elif type_name in self.model_db.types:
                model = self.model_db.types[type_name]
                if isinstance(model, EnumModel):
                    return 0
                else:
                    from pylmcp import Object
                    return Object(class_name=model, randomize=True)
            else:
                raise Exception("%s not implemented" % type_name)

        if self.is_array:
            if self.is_static_array:
                return [random_simple_value(self.attr_type)] * \
                    self.max_array_length
            else:
                return [random_simple_value(self.attr_type),
                        random_simple_value(self.attr_type)]
        else:
            return random_simple_value(self.attr_type)

    @classmethod
    def from_xml(cls, node, object_class, model_db):
        optional = node.attrib.get('Optional', "false") == "true"
        is_large_array = node.attrib.get('LargeArray', "false") == "true"
        attr_type = node.attrib['Type']
        series = node.attrib.get('Series')

        max_array_length = None
        min_array_length = None

        m = re.search(r'^(.+)\[([0-9]+)?\]$', attr_type)
        if m is not None:
            attr_type = m.group(1)
            if m.group(2) is not None:
                max_array_length = int(m.group(2))
                min_array_length = int(m.group(2))
            else:
                max_array_length = node.attrib.get('MaxArrayLength')
                min_array_length = 0

        if "/" not in attr_type:
            if series is not None:
                attr_type = "%s/%s" % (series, attr_type)
            elif attr_type not in cls.BASIC_TYPES:
                attr_type = "%s/%s" % (object_class.name, attr_type)

        return cls(
            attr_type=attr_type,
            name=node.attrib['Name'],
            units=node.attrib.get('Units'),
            min_array_length=min_array_length,
            max_array_length=max_array_length,
            is_large_array=is_large_array,
            optional=optional,
            object_class=object_class,
            model_db=model_db)

    def unpack(self, payload):

        def unpack_simple_type(type_name, payload):
            value = None

            if type_name in payload.SUPPORTED_TYPES:
                value = payload.unpack(type_name)
            else:
                # This is not a simple type so check in the database
                obj_type = self.model_db.types[type_name]
                if isinstance(obj_type, EnumModel):
                    value = payload.unpack("int32")
                else:
                    from pylmcp import Object
                    value = Object.unpack(payload)
            return value

        if self.is_array:
            # This is an array first unpack the bounds if necessary
            if self.is_static_array:
                array_size = self.min_array_length
            else:
                if self.is_large_array:
                    array_size = payload.unpack("uint32")
                else:
                    array_size = payload.unpack("uint16")

            value = []
            for idx in range(array_size):
                value.append(unpack_simple_type(self.attr_type, payload))
            return value
        else:
            return unpack_simple_type(self.attr_type, payload)
