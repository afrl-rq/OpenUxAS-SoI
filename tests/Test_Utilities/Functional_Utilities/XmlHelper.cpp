//// ===============================================================================
//// Authors: AFRL/RQQA
//// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
//// 
//// Copyright (c) 2017 Government of the United State of America, as represented by
//// the Secretary of the Air Force.  No copyright is claimed in the United States under
//// Title 17, U.S. Code.  All Other Rights Reserved.
//// ===============================================================================
//
///* 
// * File:   XmlHelper.cpp
// * Author: jon
// * 
// * Created on October 24, 2018, 1:05 PM
// */
//
//#include <vector>
//#include <string>
//#include <iostream>
//#include "XmlHelper.h"
//
//XmlHelper::XmlHelper(std::string xmlStringRepresentation){
//    rootNode = stringToXmlNode(xmlStringRepresentation);
//}
//
//XmlHelper::XmlHelper(pugi::xml_document xmlDocument) {
//	document = &xmlDocument;
//	rootNode = document->document_element();
//}
//
//XmlHelper::XmlHelper(const XmlHelper& orig) {
//}
//
//XmlHelper::~XmlHelper() {
//	delete document;
//	document = NULL;
//}
//
////looks for a particular node by the tag string then returns the text (returns the first if there are many)
//std::string XmlHelper::GetFirstTagText(std::string childTagName)
//{
//    std::vector<pugi::xml_node> matchingDescendentNodes = GetDescendentsByName(childTagName);
//    //get the text of the first match in GetdDescendentsByName
//    if (matchingDescendentNodes.size() > 0){
//        return std::string(matchingDescendentNodes.front().text().get());
//    }else {
//        throw "Failure in XmlHelper::GetFirstTagText\n\tNo matching descendent nodes!";
//    }
//}
//
////looks for a particular node by the tag string, then returns the text (returns all)
//std::vector<std::string> XmlHelper::GetAllMatchingTagsText(std::string childTagName)
//{
//    std::vector<std::string> matchedTagsText;
//	std::vector<pugi::xml_node> matchingTags = getDescendentsOfNodeByName(rootNode, childTagName);
//	if (matchingTags.size() > 0) {
//		for (auto tag : matchingTags) {
//			matchedTagsText.push_back(std::string(tag.text().get()));
//		}
//	}
//	else {
//		throw "Failure in XmlHelper::GetAllMatchingTagsText\n\tNo matching descendent nodes!";
//	}
//    return matchedTagsText;
//}
//
////Note: static function
//bool XmlHelper::DoNodesMatch(pugi::xml_node firstNode, pugi::xml_node secondNode)
//{
//    //first check if the children nodes are the same (depth first check)
//    auto children = firstNode.children();
//    for (auto child : children) {
//        //first check children of children
//        if (std::string(child.name()) == "")
//            continue;
//        auto secondNodeMatchingChild = secondNode.child(child.name());
//        if(!DoNodesMatch(child, secondNodeMatchingChild)) // should this also check DoNodesMatch(secondNodeMatchingChild, child)?
//            return false;
//    }
//    //check attributes and text of the current node
//    //first check attributes
//    auto firstNodeAttributes = firstNode.attributes();
//    for (auto attribute : firstNodeAttributes) {
//        auto matchingAttribute = secondNode.attribute(attribute.name());
//        auto firstAttributeValue = std::string(attribute.value());
//        auto secondAttributeValue =  std::string(matchingAttribute.value());
//        if(!(firstAttributeValue == secondAttributeValue))
//            return false;
//    }
//    //now check text
//    auto firstText = std::string(firstNode.text().get());
//    auto secondText = std::string(secondNode.text().get());
//    if(!(firstText == secondText))//if the nodes' text does not match, then return false
//        return false;
//    return true;
//}
//
//std::vector<pugi::xml_node> XmlHelper::GetDescendentsByName(std::string name) {
//	return getDescendentsOfNodeByName(rootNode, name);
//}
//
//std::vector<pugi::xml_node> XmlHelper::getDescendentsOfNodeByName(pugi::xml_node node, std::string name)
//{
//    const auto children = node.children();
//    std::vector<pugi::xml_node> matchedNodes;
//    //if ((children.begin()) == children.end()){
//    //        return matchedNodes;}
//    //for(auto child : children){
//    for(auto child = children.begin(); child != children.end(); ++child){
//	std::cout << child->name() << std::endl;
//        auto childMatchedNodes = getDescendentsOfNodeByName(*child, name);
//        for(auto childNode : childMatchedNodes){
//            matchedNodes.push_back(childNode);}
//        
//        if(std::string(child->name()) == name){
//            matchedNodes.push_back(*child);}
//    }
//    return matchedNodes;
//}
//
//void XmlHelper::SetRootNode(std::string xmlStringRepresentation) {
//	this->rootNode = stringToXmlNode(xmlStringRepresentation);
//}
//
//void XmlHelper::SetRootNode(pugi::xml_document* doc) {
//	this->document = doc;
//	this->rootNode = this->document->document_element();
//}
//
//pugi::xml_node XmlHelper::GetRootNode() {
//	return rootNode;
//}
//
//pugi::xml_node XmlHelper::stringToXmlNode(std::string xmlStringRepresentation){
//    //document->load_string(xmlStringRepresentation.c_str());
//	document->load(xmlStringRepresentation.c_str());
//	if (document->empty())
//		std::cout << "The root node is empty" << std::endl;
//	return document->document_element();
//}