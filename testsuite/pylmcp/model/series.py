from xml.etree import ElementTree
from pylmcp.model.object_class import ObjectClass
from pylmcp.model.enum import EnumModel
import logging
import typing
from typing import Dict

if typing.TYPE_CHECKING:
    from pylmcp.model import ModelDatabase


logger = logging.getLogger('pylmcp.series')


class Series(object):

    def __init__(self,
                 name: str,
                 namespace: str,
                 version: int,
                 model_db: "ModelDatabase") -> None:
        """Initialize a series.

        :param name: series name
        :param namespace: namespace
        :param version: version
        :param model_db: the model database
        """
        self.name = name
        self.namespace = namespace
        self.version = version
        self.classes: Dict[str, ObjectClass]= {}
        self.enums: Dict[str, EnumModel] = {}
        self.model_db = model_db

        # Compute series id
        series_name_ext = self.name + '\0' * (8 - len(self.name))
        self.id = 0
        for c in series_name_ext:
            self.id = self.id * 256 + ord(c)

    def add_struct(self, struct):
        self.classes[struct.name] = struct

    def add_enum(self, enum):
        self.enums[enum.name] = enum

    @classmethod
    def load_model(cls, path, model_db):
        tree = ElementTree.parse(path)
        return cls.from_xml(tree.getroot(), model_db=model_db)

    @classmethod
    def from_xml(cls, node, model_db):
        assert node.tag == 'MDM'

        series = None
        namespace = None
        version = None
        struct_list = []
        enum_list = []

        for child in node:
            if child.tag == 'SeriesName':
                name = child.text
            elif child.tag == 'Namespace':
                namespace = child.text
            elif child.tag == 'Version':
                version = int(child.text)
            elif child.tag == 'StructList':
                struct_list = [c for c in child]
            elif child.tag == 'EnumList':
                enum_list = [c for c in child]
            else:
                logger.error('ignoring %s', child.tag)

        series = cls(name=name,
                     namespace=namespace,
                     version=version,
                     model_db=model_db)

        for idx, struct in enumerate(struct_list):
            series.add_struct(
                ObjectClass.from_xml(
                    node=struct,
                    series=series,
                    model_db=model_db,
                    id=idx + 1))
        for enum in enum_list:
            series.add_enum(EnumModel.from_xml(node=enum))
        return series

    def __str__(self):
        return "series: %s, namespace: %s" % (self.name, self.namespace)
