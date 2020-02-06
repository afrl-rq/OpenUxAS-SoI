import struct
import typing
from typing import Tuple, List, Optional
from pylmcp.model.object_attr import ObjectAttr

if typing.TYPE_CHECKING:
    import pylmcp.model
    import pylmcp.model.series
    import pylmcp.util


class ObjectClass(object):
    """Message class (i.e: Struct)."""

    def __init__(self,
                 name: str,
                 id: int,
                 extends: typing.Optional[str],
                 attrs: typing.List[ObjectAttr],
                 series: "pylmcp.model.series.Series",
                 model_db: "pylmcp.model.ModelDatabase") -> None:
        """Initialize an LMCP class.

        :param name: class name
        :param id: an integer id for the class
        :param extends: a class name from which this class is derived.
            The class name is in the format SERIES_NAME/CLASS_NAME
        :param attrs: a list of ObjAttr instance defining the attributes
            for the this class
        :param series: the series in which this class is defined
        :param model_db: the model database
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
    def attrs(self) -> typing.List[ObjectAttr]:
        """Return the full list of attributes.

        :return: the complete list of attributes (including the attributes
            declared in the parent classes)
        """
        result: typing.List[ObjectAttr] = []
        if self.extends:
            result += self.model_db.types[self.extends].attrs
        result += self.__attrs
        return result

    @property
    def full_id(self) -> Tuple[int, int, int]:
        """Return a tuple that represents the full class id."""
        return (self.series_id, self.id, self.version)

    @property
    def series_id(self) -> int:
        """Return the series id."""
        return self.series.id

    @property
    def series_name(self) -> str:
        """Return the series name."""
        return self.series.name

    @property
    def namespace(self) -> str:
        """Return the namespace in which the class is declared."""
        return self.series.namespace

    @property
    def version(self) -> int:
        """The class version (i.e same as series version)."""
        return self.series.version

    def pack(self,
             value: dict,
             include_headers: bool = True) -> bytes:
        """Pack the message into its binary format.

        :param value: attribute's values
        :param include_headers: add LMCP header
        :return: the binary representation
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
                sum += result[x] & 0xFF
            result += struct.pack(">I", sum)
            return result
        else:
            return result

    @classmethod
    def unpack(self,
               payload: "pylmcp.util.Buffer") -> Optional[Tuple[int, int, int]]:
        exists = payload.unpack("bool")
        if not exists:
            return None
        else:
            full_id = typing.cast(
                Tuple[int, int, int],
                payload.unpack_struct(">qIH"))
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

    def __str__(self) -> str:
        return "\n".join(["lmcp_type:           %s" % self.id,
                          "series_name:         %s" % self.series_name,
                          "full_lmcp_type_name: %s" % self.full_name])
