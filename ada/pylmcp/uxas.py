import os
import tempfile
from contextlib import closing
from xml.etree.ElementTree import Element as xml_el, \
    SubElement as xml_sub, \
    tostringlist as xml_dump
from e3.os.fs import which
from e3.fs import rm
from e3.os.process import Run

ALL_MESSAGES = "abcdefghijklmnopqrstuvwxyz" + \
    "ABCDEFGHIJKLMNOPQRSTUVWXYZ"


class PublishPullBridge(object):
    """PublishPullBridge service."""

    def __init__(self,
                 pub_address='tcp://*:5560',
                 pull_address='tcp://*:5561'):
        """Initialize a PublishPull bridge

        :param pub_address: publication address
        :type pub_address: str
        :param pull_address: pull address
        :type pull_address: str
        """
        self.publish_address = pub_address
        self.pull_address = pull_address

    def as_xml(self):
        """Return service configuration as xml node.

        :return: the xml node for the service configuration
        :rtype: xml.etree.Element
        """
        result = xml_el(
            'Bridge',
            attrib={'Type': 'LmcpObjectNetworkPublishPullBridge',
                    'AddressPUB': self.publish_address,
                    'AddressPULL': self.pull_address})
        for c in ALL_MESSAGES:
            xml_sub(
                result,
                'SubscribeToMessage',
                attrib={'MessageType': c})
        return result


class SubscribePushBridge(object):
    """SubcribePush network bridge."""

    def __init__(self,
                 sub_address='tcp://localhost:5560',
                 push_address='tcp://localhost:5561'):
        """Initialize a SubscribePush bridge

        :param sub_address: publication address
        :type sub_address: str
        :param push_address: pull address
        :type push_address: str
        """
        self.sub_address = sub_address
        self.push_address = push_address

    def as_xml(self):
        """Return service configuration as xml node.

        :return: the xml node for the service configuration
        :rtype: xml.etree.Element
        """
        result = xml_el(
            'Bridge',
            attrib={'Type': 'LmcpObjectNetworkSubscribePushBridge',
                    'AddressSUB': self.sub_address,
                    'AddressPUSH': self.push_address})
        for c in ALL_MESSAGES:
            xml_sub(
                result,
                'SubscribeToExternalMessage',
                attrib={'MessageType': c})
            xml_sub(
                result,
                'SubscribeToMessage',
                attrib={'MessageType': c})
        return result


class AutomationRequestValidator(object):
    """AutomationRequest Validation service."""

    def __init__(self):
        pass

    def as_xml(self):
        """Return service configuration as xml node.

        :return: the xml node for the service configuration
        :rtype: xml.etree.Element
        """
        result = xml_el(
            'Service',
            attrib={'Type': 'AutomationRequestValidatorService'})
        return result


class UxASConfig(object):
    """An UxAS instance configuration."""

    def __init__(self, entity_id=100, entity_type='Aircraft'):
        """Initialize a configuration.

        :param entity_id: entity id
        :type entity_id: str
        :param entity_type: entity_type
        :type entity_type: str
        """
        self.elements = []
        self.entity_id = entity_id
        self.entity_type = entity_type

    def __iadd__(self, el):
        """Add a configuration element.

        :param el: a configuration element
        :type el: UxASConfigElement
        """
        self.elements.append(el)
        return self

    def dump(self):
        """Get configuration as xml string.

        :return: the configuration content
        :rtype: str
        """
        result = xml_el(
            'UxAS',
            attrib={'FormatVersion': '1.0',
                    'EntityID': str(self.entity_id),
                    'EntityType': self.entity_type})

        for el in self.elements:
            result.append(el.as_xml())

        result = b'<?xml version="1.0" encoding="UTF-8" standalone="yes" ?>\n' + \
            b"\n".join(xml_dump(result))
        return result


class UxAS(object):
    """An UxAS instance."""

    def __init__(self,
                 entity_id,
                 entity_type='Aircraft',
                 uxas_bin=None):
        """Initialize an UxAS instance.

        :param entity_id: the entity id
        :type entity_id: str
        :param entity_type: the entity type
        :type entity_type: str
        :param uxas_bin: location of the uxas executable. If None try to find
            uxas on the path.
        :type uxas_bin: str | None
        """
        if uxas_bin is None:
            self.uxas_bin = which('uxas')
        else:
            self.uxas_bin = uxas_bin

        self.cfg_path = None
        self.cfg = UxASConfig(entity_id, entity_type)
        self.process = None

    def run(self):
        """Launch the UxAS instance.

        :return: the process object
        :rtype: e3.os.process.Run
        """
        with closing(tempfile.NamedTemporaryFile(mode='wb',
                                                 delete=False)) as fd:
            self.cfg_path = fd.name
            fd.write(self.cfg.dump())

        self.process = Run(
            [self.uxas_bin, '-cfgPath', self.cfg_path],
            output=None,
            bg=True)
        return self.process

    def interrupt(self):
        """Interrupt the UxAS instance."""
        if self.process is not None and self.process.is_running:
            self.process.interrupt()

        if os.path.isfile(self.cfg_path):
            rm(self.cfg_path)
