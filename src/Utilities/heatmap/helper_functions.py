def indent(elem, level=0):
    # Helper function used to properly format the xml file
    i = "\n" + level * "  "
    if len(elem):
        if not elem.text or not elem.text.strip():
            elem.text = i + "  "
        if not elem.tail or not elem.tail.strip():
            elem.tail = i
        for elem in elem:
            indent(elem, level + 1)
        if not elem.tail or not elem.tail.strip():
            elem.tail = i
    else:
        if level and (not elem.tail or not elem.tail.strip()):
            elem.tail = i


def does_elem_exist(root, tag, tagtag, atr, art_text):
    for elem in root.iter(tag):
        for elem_elem in elem.iter(tagtag):
            if elem_elem.attrib[atr] == art_text:
                return 1
                print('EXISTS: ' + tagtag + " " + art_text)
                break
    return 0
