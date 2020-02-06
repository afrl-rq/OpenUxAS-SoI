import json
import re
import typing
from typing import Dict, Any, Optional
from pylmcp.model import LMCP_DB
from pylmcp.util import Buffer
from pylmcp.model.object_class import ObjectClass


class InvalidObjectClass(Exception):
    pass

class Object(object):
    """A LMCP Object."""

    DB = LMCP_DB

    def __init__(self,
                 class_name: typing.Union[str, ObjectClass],
                 randomize: bool = False,
                 **kwargs):
        """Initialize a LMCP Object.

        :param class_name: an object class name (partial name accepted)
        :type class_name: str | ObjectClass
        :param randomize: if True non set attributes are created
            randomly
        :type randomize: bool
        :param kwargs: user can set any valid attribute for the class
        """

        if isinstance(class_name, ObjectClass):
            self.object_class = class_name
        else:
            object_class = [k for k in self.DB.classes.keys()
                            if k.endswith(class_name)]
            if len(object_class) == 0:
                raise InvalidObjectClass("invalid class: %s" % class_name)
            elif len(object_class) > 1:
                raise InvalidObjectClass(
                    "ambiguous class name: %s" % class_name)

            self.object_class = self.DB.classes[object_class[0]]
        self.data: Dict[str, Any] = {}

        # Initialize to None every attributes
        for f in self.attributes:
            self.data[f.name] = None

        # Handle kwargs
        for k, v in kwargs.items():
            if k not in self.data:
                raise AttributeError(
                    "attribute %s is not valid (valid attributes: %s)" %
                    (k, self.data.keys()))
            else:
                self.data[k] = v

        # set random attributes
        if randomize:
            for f in self.attributes:
                if f.name not in kwargs:
                    self.data[f.name] = f.random_value()

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

    def __getitem__(self, key):
        return self.data[key]

    def as_dict(self) -> Dict[str, Any]:
        result: Dict[str, Any] = {}
        for k, v in self.data.items():
            if isinstance(v, list):
                result[k] = []
                for el in v:
                    if isinstance(el, Object):
                        result[k].append(el.as_dict())
                    else:
                        result[k].append(el)
            elif isinstance(v, Object):
                result[k] = v.as_dict()
            else:
                result[k] = v
        return result

    def __str__(self):
        return json.dumps(self.as_dict(), indent=2)

    def __eq__(self, other):
        # First ensure that other is an Object
        if not isinstance(other, Object):
            return False

        # Ensure that lmcp class are equals
        if self.object_class.name != other.object_class.name:
            return False

        # Finally check if data associated with the object
        # is equal
        return self.data == other.data

    def __neq__(self, other):
        return not (self == other)

    def set_attributes_randomly(self) -> None:
        """Set object attributes randomly."""
        for f in self.attributes:
            self.data[f.name] = f.random_value()

    @property
    def attributes(self):
        return self.object_class.attrs

    @property
    def attribute_names(self) -> typing.List[str]:
        return [f.name for f in self.object_class.attrs]

    def pack(self) -> bytes:
        return self.object_class.pack(value=self.data)

    @classmethod
    def unpack(cls, data: Buffer) -> Optional["Object"]:
        full_id = ObjectClass.unpack(data)
        if full_id is None:
            return None

        object_class = cls.DB.class_ids[full_id]
        result = cls(class_name=object_class.full_name)

        for attr in object_class.attrs:
            value = attr.unpack(data)
            result.data[attr.name] = value
        return result
