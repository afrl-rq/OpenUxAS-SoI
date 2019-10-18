class EntryModel(object):
    def __init__(self, name, value):
        self.name = name
        self.value = value

    @classmethod
    def from_xml(cls, node, default_value=None):
        return cls(
            name=node.attrib['Name'],
            value=node.attrib.get('Value', default_value))


class EnumModel(object):
    def __init__(self, name, entries=None):
        self.name = name
        self.entries = entries

    @classmethod
    def from_xml(cls, node):
        entries = []
        default_value = 0
        for child in node:
            entries.append(EntryModel.from_xml(child,
                                               default_value=default_value))
            default_value += 1

        return cls(
            name=node.attrib['Name'],
            entries=entries)
