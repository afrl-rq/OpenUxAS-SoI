"""Handle a database of LMCP messages descriptions.

The module allows to create a database containing the description of all
objects and enums available.

A LMCP model database contains a list of "Series" (i.e: correspond to one XML
file). Each Series contains a list of classes and enums defined in the XML
file.

By default a database is computed with all xml files present in the xml_models
subdirectory. The pylmcp.Object class (used to create instance of objects) use
by default this database
"""

import os
from e3.fs import ls
from pylmcp.model.series import Series


class ModelDatabase(object):
    """Gather all the LMCP models."""

    def __init__(self):
        """Initialize the database."""
        self.series = {}

        # Available classes indexed by their full lmcp name. (dot notation)
        self.classes = {}

        # Available classes indexed by their interger triplet
        # (series_num, type_num, version)
        self.class_ids = {}

        # Available types (classes and enums) indexed by xml
        # name (SERIES_NAME/NAME)
        self.types = {}

    def add_series(self,
                   series: Series) -> None:
        """Add a series.

        :param series: the series to add in the database
        :type series: pylmcp.model.series.Series
        """
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

    @classmethod
    def load_series_from_dir(cls, path: str) -> 'ModelDatabase':
        """Load all series as xml files from a given directory.
        
        :param path: the directory containing the list of xml models
        :type path: str
        :return: a model database
        :rtype: pylmcp.model.ModelDatabase
        """
        model_db = cls()
        for xml_model in ls(os.path.join(path, '*.xml')):
            model_db.add_series(
                Series.load_model(xml_model, model_db=model_db))
        return model_db


# Initialize the default LMCP database model
MODEL_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                         'xml_models')
LMCP_DB = ModelDatabase.load_series_from_dir(MODEL_DIR)
