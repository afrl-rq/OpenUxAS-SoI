import json
import struct
from pylmcp.model import LMCP_DB


class Object(object):
    """A LMCP Object."""

    DB = LMCP_DB

    def __init__(self, class_name, **kwargs):
        """Initialize a LMCP Object.

        :param class_name: an object class name
        :type class_name: str
        """
        self.object_class = self.DB.classes[class_name]
        self.data = {}

        # Initialize to None every attributes
        for f in self.attributes:
            self.data[f.name] = None

    def __getattr__(self, name):
        try:
            return self.data[name]
        except KeyError as e:
            raise AttributeError(e)

    def __setattr__(self, name, value):
        if name in ('object_class', 'data'):
            object.__setattr__(self, name, value)
        elif name in self.attribute_list:
            self.data[name] = value
        else:
            raise AttributeError("invalid attribute: %s" % name)

    def __str__(self):
        return json.dumps(self.data, indent=2)

    def set_attributes_randomly(self):
        """Set object attributes randomly."""
        for f in self.attributes:
            self.data[f.name] = f.random_value()

    @property
    def attributes(self):
        print("Here %s" % self.object_class)
        return self.object_class.attrs

    @property
    def attribute_names(self):
        return [f.name for f in self.object_class.attrs]

    def pack(self):
        return self.object_class.pack(value=self.data)

    @classmethod
    def unpack(cls, data):
        unpack_header_str = ">IIBqIH"
        ctrl, size, is_valid, series_id, type_id, version = \
            struct.unpack_from(unpack_header_str, data, 0)
        pos = struct.calcsize(unpack_header_str)
        object_class = cls.DB.class_ids[(series_id, type_id, version)]

        for attr in object_class.attrs:
            size, value = attr.unpack(data, pos)
            pos += size
            print "%-32s, %6d, %s" % (attr.name, size, value)
