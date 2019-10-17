import os
from e3.fs import ls
from pylmcp.model.series import Series

class ModelDatabase(object):
    """Gather all the LMCP models."""

    def __init__(self):
        """Initialize the database."""
        self.series = {}

        # Available classes indexed by their full lmcp name
        self.classes = {}

        # Available classes indexed by their interger triplet
        # (series_num, type_num, version)
        self.class_ids = {}

        # Available types (classes and enums) indexed by xml
        # name (SERIES_NAME/NAME)
        self.types = {}

    def add_series(self, series):
        # Register the series
        self.series[series.name] = series

        # Update index
        self.classes.update(
            {cls.full_name: cls
             for cls in series.classes.values()})

        # Update types and class_ids
        for m in series.classes.values():
            self.class_ids[(m.series_id, m.id, m.version)] = m
            self.types["%s/%s" % (series.name, m.name)] = m

        for e in series.enums.values():
            self.types["%s/%s" % (series.name, e.name)] = e

    def new_msg(self, type_name):
        return Object(self.structs[type_name])

    @classmethod
    def load_series_from_dir(cls, path):
        model_db = cls()
        for xml_model in ls(os.path.join(path, '*.xml')):
            model_db.add_series(
                Series.load_model(xml_model, model_db=model_db))
        return model_db

    def unpack_msg(self, payload):
        unpack_str = ">IIBqIH"
        ctrl, size, is_valid, series_num, type_num, version = struct.unpack_from(unpack_str, payload, 0)
        struct_model = self.struct_ids[(series_num, type_num, version)]
        return Message.unpack(struct_model,
                              payload,
                              pos=struct.calcsize(unpack_str))

# Initialize the default LMCP database model
MODEL_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                         'xml_models')
LMCP_DB = ModelDatabase.load_series_from_dir(MODEL_DIR)
