import struct
from pylmcp.model.object_attr import ObjectAttr


class ObjectClass(object):
    """Message class (i.e: Struct)."""

    def __init__(self, name, id, extends, attrs, series, model_db):
        """Initialize an LMCP class.

        :param name: class name
        :type name: str
        :param id: an integer id for the class
        :type id: int
        :param extends: a class name from which this class is derived.
            The class name is in the format SERIES_NAME/CLASS_NAME
        :type extends: str | None
        :param attrs: a list of ObjAttr instance defining the attributes
            for the this class
        :type attrs: list[pylmcp.model.obj_attr.ObjectAttr]
        :param series: the series in which this class is defined
        :type series: pylmcp.model.series.Series
        :param model_db: the model database
        :type model_db: pylmcp.model.ModelDatabase
        """
        self.name = name
        self.__attrs = attrs
        self.extends = extends
        self.series = series
        self.model_db = model_db
        self.id = id

        # Full type name in dot notation
        self.full_name = "%s.%s" % (self.namespace.replace('/', '.'), name)

    @property
    def attrs(self):
        """Return the full list of attributes.

        :return: the complete list of attributes (including the attributes
            declared in the parent classes)
        :rtype: list[pylmcp.model.obj_attr.ObjectAttr
        """
        result = []
        if self.extends:
            result += self.model_db.types[self.extends].attrs
        result += self.__attrs
        return result

    @property
    def full_id(self):
        """Return a tuple that represents the full class id.

        :rtype: (int, int, int)
        """
        return (self.series_id, self.id, self.version)

    @property
    def series_id(self):
        """Return the series id.

        :rtype: int
        """
        return self.series.id

    @property
    def series_name(self):
        """Return the series name.

        :rtype: str
        """
        return self.series.name

    @property
    def namespace(self):
        """Return the namespace in which the class is declared.

        :rtype: str
        """
        return self.series.namespace

    @property
    def version(self):
        """The class version (i.e same as series version)

        :rtype: int
        """
        return self.series.version

    def pack(self, value, include_headers=True):
        """Pack the message into its binary format.

        :param value: attribute's values
        :type value: dict
        :param include_headers: add LMCP header
        :type include_headers: bool
        :return: the binary representation
        :rtype: string
        """

        # Starts with the object type
        result = struct.pack(">qIH", *self.full_id)

        # Followed by the attributes
        for attr in self.attrs:
            result += attr.pack(value=value[attr.name])

        if include_headers:
            # ??? not complete ???. The constant there should be computed
            header = struct.pack(">iIB", 1280131920, len(result), 1)
            result = header + result
            # Compute the final checksum and append it
            sum = 0
            for x in range(len(result)):
                sum += ord(result[x]) & 0xFF
            result += struct.pack(">I", sum)
            return result
        else:
            return result

    @classmethod
    def unpack(self, payload):
        exists = payload.unpack("bool")
        if not exists:
            return None
        else:
            full_id = payload.unpack_struct(">qIH")
            return full_id

    @classmethod
    def from_xml(cls, node, id, series, model_db):
        # Parse the object attributes
        attrs = []
        for attr in node:
            attrs.append(ObjectAttr.from_xml(attr, series, model_db))

        # Get the the parent class
        extends = node.attrib.get('Extends', None)
        series_name = node.attrib.get('Series', None)
        if extends is not None:
            if "/" not in extends:
                if series_name is not None:
                    extends = "%s/%s" % (series_name, extends)
                else:
                    extends = "%s/%s" % (series.name, extends)

        # Return the new class
        return cls(
            name=node.attrib['Name'],
            id=id,
            extends=extends,
            attrs=attrs,
            series=series,
            model_db=model_db)

    def __str__(self):
        return "\n".join(["lmcp_type:           %s" % self.id,
                          "series_name:         %s" % self.series_name,
                          "full_lmcp_type_name: %s" % self.full_name])
