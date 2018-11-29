// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   XmlHelper.h
 * Author: jon
 *
 * Created on October 24, 2018, 1:05 PM
 */

#ifndef XMLHELPER_H
#define XMLHELPER_H
#include <pugixml.hpp>
#include <string>
#include <vector>

class XmlHelper {
public:

XmlHelper(std::string xmlStringRepresentation){
    rootNode = stringToXmlNode(xmlStringRepresentation);
}

XmlHelper(pugi::xml_document xmlDocument) {
	document = &xmlDocument;
	rootNode = document->document_element();
}

XmlHelper(const XmlHelper& orig) {
}

~XmlHelper() {
	delete document;
	document = NULL;
}

//looks for a particular node by the tag string then returns the text (returns the first if there are many)
std::string GetFirstTagText(std::string childTagName)
{
    std::vector<pugi::xml_node> matchingDescendentNodes = GetDescendentsByName(childTagName);
    //get the text of the first match in GetdDescendentsByName
    if (matchingDescendentNodes.size() > 0){
        return std::string(matchingDescendentNodes.front().text().get());
    }else {
        throw "Failure in XmlHelper::GetFirstTagText\n\tNo matching descendent nodes!";
    }
}

//looks for a particular node by the tag string, then returns the text (returns all)
std::vector<std::string> GetAllMatchingTagsText(std::string childTagName)
{
    std::vector<std::string> matchedTagsText;
	std::vector<pugi::xml_node> matchingTags = getDescendentsOfNodeByName(rootNode, childTagName);
	if (matchingTags.size() > 0) {
		for (auto tag : matchingTags) {
			matchedTagsText.push_back(std::string(tag.text().get()));
		}
	}
	else {
		throw "Failure in XmlHelper::GetAllMatchingTagsText\n\tNo matching descendent nodes!";
	}
    return matchedTagsText;
}

//Note: static function
static bool DoNodesMatch(pugi::xml_node firstNode, pugi::xml_node secondNode)
{
    //first check if the children nodes are the same (depth first check)
    auto children = firstNode.children();
    for (auto child : children) {
        //first check children of children
        if (std::string(child.name()) == "")
            continue;
        auto secondNodeMatchingChild = secondNode.child(child.name());
        if(!DoNodesMatch(child, secondNodeMatchingChild)) // should this also check DoNodesMatch(secondNodeMatchingChild, child)?
            return false;
    }
    //check attributes and text of the current node
    //first check attributes
    auto firstNodeAttributes = firstNode.attributes();
    for (auto attribute : firstNodeAttributes) {
        auto matchingAttribute = secondNode.attribute(attribute.name());
        auto firstAttributeValue = std::string(attribute.value());
        auto secondAttributeValue =  std::string(matchingAttribute.value());
        if(!(firstAttributeValue == secondAttributeValue))
            return false;
    }
    //now check text
    auto firstText = std::string(firstNode.text().get());
    auto secondText = std::string(secondNode.text().get());
    if(!(firstText == secondText))//if the nodes' text does not match, then return false
        return false;
    return true;
}

//get the descendents of the current XmlHelper's tree by name
std::vector<pugi::xml_node> GetDescendentsByName(std::string name) {
	return getDescendentsOfNodeByName(rootNode, name);
}

// Setter for the root node based on a string representation of the xml
void SetRootNode(std::string xmlStringRepresentation) {
	this->rootNode = stringToXmlNode(xmlStringRepresentation);
}

// Setter for the xml helpers root node through a document. Allows a single XmlHelper service to be used for tests
void SetRootNode(pugi::xml_document* doc) {
	this->document = doc;
	this->rootNode = this->document->document_element();
}

// Returns the root node of the xml tree
pugi::xml_node GetRootNode() {
	return rootNode;
}

private:
    //the root node searched in the xml helper class
    pugi::xml_node rootNode;

    //the document containing the root node. Note: the document must be stored, otherwise the xml_nodes will not exist
    pugi::xml_document* document = new pugi::xml_document();
    
    // converts a string to an xml node
    pugi::xml_node stringToXmlNode(std::string xmlStringRepresentation){
	document->load(xmlStringRepresentation.c_str());
	if (document->empty())
		std::cout << "The root node is empty" << std::endl;
	return document->document_element();
    }
    
    // gets the descendents of a node by the descendents name
    std::vector<pugi::xml_node> getDescendentsOfNodeByName(pugi::xml_node node, std::string name)
    {
        const auto children = node.children();
        std::vector<pugi::xml_node> matchedNodes;
        for(auto child = children.begin(); child != children.end(); ++child){
            std::cout << child->name() << std::endl;
            auto childMatchedNodes = getDescendentsOfNodeByName(*child, name);
            for(auto childNode : childMatchedNodes){
                matchedNodes.push_back(childNode);}

            if(std::string(child->name()) == name){
                matchedNodes.push_back(*child);}
        }
        return matchedNodes;
    }

};

#endif /* XMLHELPER_H */
