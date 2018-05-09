// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#include <sstream>
#include <fstream>
#include <iostream>
#include <vector>
#include <string>
#include <ctime>
#include <cstdint>

#include <stdlib.h>

#ifndef ALGEBRA_BASE_H
#define ALGEBRA_BASE_H

namespace uxas
{
namespace common
{
namespace utilities
{

// TYPE DEFINITIONS
typedef int64_t action_t;
typedef std::vector <action_t> v_action_t;


typedef enum _nodeType_t {
  ND_UNDEFINED = 0,
  ND_ACTION,
  ND_OPERATOR
} nodeType_t;


typedef enum _operatorType_t {
  OP_UNDEFINED = 0,
  OP_SEQUENTIAL,
  OP_ALTERNATIVE,
  OP_PARALLEL,
  OP_TILDE
} operatorType_t;


// CLASS DEFINITIONS
class parseTreeNode
{
public:
	virtual ~parseTreeNode() { }
    parseTreeNode *parent;
    virtual v_action_t nextActions ( const v_action_t &executedActions, bool &encounterExecutedOut );
    virtual nodeType_t getNodeType ( void );
    virtual v_action_t getChildrenActions ( void );
    virtual void deleteTree (void);
    virtual parseTreeNode *searchAction (action_t actionIDIn);

    virtual int randomlyShuffleChildren (double suffleProb);
};


class actionNode:public parseTreeNode
{
private:
    action_t actionNo;
public:
    actionNode (action_t actionNoIn);
    action_t getActionID (void);
    virtual v_action_t nextActions ( const v_action_t &executedActions, bool &encounterExecutedOut );
    virtual nodeType_t getNodeType (void );
    virtual v_action_t getChildrenActions ( void );
    virtual void deleteTree (void);    
    virtual parseTreeNode *searchAction (action_t actionIDIn);

    virtual int randomlyShuffleChildren (double suffleProb);
};


class operatorNode:public parseTreeNode
{
private:
    int numNodes;
    operatorType_t operatorType;
    std::vector <parseTreeNode*> nodePointers;
public:
    operatorNode (void);
    int setOperatorType (operatorType_t operatorTypeIn);
    operatorType_t getOperatorType (void);
    int addNode (parseTreeNode *nodePointer);
    int getNumNodes (void);
    parseTreeNode *getNodePointer (int nodeNo);
    virtual v_action_t nextActions ( const v_action_t &executedActions, bool &encounterExecutedOut );
    virtual nodeType_t getNodeType (void );
    virtual v_action_t getChildrenActions ( void );
    virtual void deleteTree (void);
    virtual parseTreeNode *searchAction (action_t actionIDIn);
    
    virtual int randomlyShuffleChildren (double suffleProb);
};


class CAlgebraBase 
{
public:
    v_action_t actions;
    std::vector <v_action_t> preds;
    parseTreeNode *parseTreeRoot;
    bool checkFormulaSyntax(const std::string testString);
    parseTreeNode* parseFormula(std::string formula);
    void initPredsRec (parseTreeNode *ptRoot);
    int findActionIndexviaActionID (action_t actionID);

    int randomlyShuffleTree (double shuffleProb);    
};

}; //namespace log
}; //namespace common
}; //namespace uxas

#endif  //ALGEBRA_BASE_H
