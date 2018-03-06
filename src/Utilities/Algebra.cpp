// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#include "Algebra.h"



#define COUT_INFO_MSG(MESSAGE) std::cout << "<>Algebra:" << MESSAGE << std::endl;std::cout.flush();
#define COUT_FILE_LINE_MSG(MESSAGE) std::cout << "<>Algebra:" << __FILE__ << ":" << __LINE__ << ":" << MESSAGE << std::endl;std::cout.flush();
#define CERR_FILE_LINE_MSG(MESSAGE) std::cerr << "<>Algebra:" << __FILE__ << ":" << __LINE__ << ":" << MESSAGE << std::endl;std::cerr.flush();

namespace uxas
{
namespace common
{
namespace utilities
{




v_action_t parseTreeNode::nextActions(const v_action_t &executedActions, bool &encounterExecutedOut)
{
    v_action_t searchResultThis;
    return searchResultThis;
}

nodeType_t parseTreeNode::getNodeType(void)
{
    nodeType_t nodeType(ND_UNDEFINED);
    return nodeType;
}

v_action_t parseTreeNode::getChildrenActions(void)
{
    v_action_t actions;
    return actions;
}

void parseTreeNode::deleteTree(void)
{

}

parseTreeNode* parseTreeNode::searchAction(action_t actionIDIn)
{
    return NULL;
}

int parseTreeNode::randomlyShuffleChildren(double shuffleProb)
{
    return 1;
}

actionNode::actionNode(action_t actionNoIn)
{
    this->actionNo = actionNoIn;
}

action_t actionNode::getActionID(void)
{
    return actionNo;
}

v_action_t actionNode::nextActions(const v_action_t &executedActions, bool &encounterExecutedOut)
{
    v_action_t searchResultThis;
    bool actionFound = false;
    for (unsigned int i = 0; i < executedActions.size(); i++)
        if (executedActions[i] == this->actionNo)
            actionFound = true;

    if (!actionFound)
    {
        searchResultThis.push_back(this->actionNo);
        encounterExecutedOut = false;
    }
    else
    {
        encounterExecutedOut = true;
    }

    return searchResultThis;
}

nodeType_t actionNode::getNodeType(void)
{
    return ND_ACTION;
}

v_action_t actionNode::getChildrenActions(void)
{
    v_action_t v_action;
    v_action.push_back(this->actionNo);
    return v_action;
}

void actionNode::deleteTree(void)
{
    std::cout << "Deleting node : " << this->actionNo << std::endl;
}

parseTreeNode* actionNode::searchAction(action_t actionIDIn)
{
    if (actionIDIn == this->actionNo)
        return (parseTreeNode *)this;
    else
        return NULL;
}

int actionNode::randomlyShuffleChildren(double shuffleProb)
{
    return 1; // Just break the recursion
}

operatorNode::operatorNode(void)
{
    this->numNodes = 0;
    this->operatorType = OP_UNDEFINED;
}

int operatorNode::addNode(parseTreeNode *nodePointer)
{
    this->nodePointers.push_back(nodePointer);
    return 1;
}

int operatorNode::getNumNodes()
{
    return (int) this->nodePointers.size();
}

int operatorNode::setOperatorType(operatorType_t operatorTypeIn)
{
    this->operatorType = operatorTypeIn;
    return 1;
}

operatorType_t operatorNode::getOperatorType(void)
{
    return this->operatorType;
}

parseTreeNode* operatorNode::getNodePointer(int nodeNo)
{
    if ((this->nodePointers.size() == 0)
            || (nodeNo < 0)
            || (nodeNo > (signed int) this->nodePointers.size()))
    {
        return NULL;
    }

    return this->nodePointers[nodeNo];
}

v_action_t operatorNode::nextActions(const v_action_t &executedActions, bool &encounterExecutedOut)
{

    std::vector <v_action_t> searchResultChildren;

    v_action_t searchResultEmpty;

    v_action_t searchResultThis;

    for (unsigned int i = 0; i < nodePointers.size(); i++)
        searchResultChildren.push_back(searchResultEmpty);
    encounterExecutedOut = false;

    switch (this->operatorType)
    {

        case OP_SEQUENTIAL:
            encounterExecutedOut = true; // The value of this variable takes effect when
            //    i > 0 (including the case i == this->nodePointers.size()),
            //    in which case at least one children node that has been fully executed
            for (unsigned int i = 0; i < this->nodePointers.size(); i++)
            {
                bool encounterExecuted;
                searchResultChildren[i] = this->nodePointers[i]->nextActions(executedActions, encounterExecuted);
                if (searchResultChildren[i].size() > 0)
                {
                    searchResultThis = searchResultChildren[i];
                    if (i == 0) // if the left most child has actions to be executed,  
                        encounterExecutedOut = encounterExecuted; //   then return true if the child has encountered an executed action 
                    break;
                }
            }
            return searchResultThis; // notice that this is an empty std::vector if either one of the following hold
            //    (i) this->nodePointers.size () == 0  : there are no children nodes of this operator
            //    (ii) i == this->nodePointers.size () : no child node has an executable action left 
            break;

        case OP_ALTERNATIVE:
            for (unsigned int i = 0; i < this->nodePointers.size(); i++)
            {
                bool encounterExecuted;
                searchResultChildren[i] = this->nodePointers[i]->nextActions(executedActions, encounterExecuted);
                if ((encounterExecuted))
                {// && (searchResultChildren[i].size() > 0) ) {  // if an action has been encountered on this branch,
                    encounterExecutedOut = true; //   then return only the actions of this branch
                    searchResultThis = searchResultChildren[i];
                    break;
                }
            }
            if (!encounterExecutedOut)
            {
                // Collect all the possible next actions into one data structure
                for (unsigned int i = 0; i < this->nodePointers.size(); i++)
                {
                    for (unsigned int j = 0; j < searchResultChildren[i].size(); j++)
                    {
                        searchResultThis.push_back(searchResultChildren[i][j]);
                    }
                }
            }
            return searchResultThis;
            break;

        case OP_PARALLEL:
            encounterExecutedOut = false; // The value of this variable takes effect when none of the children has encountered executed
            for (unsigned int i = 0; i < this->nodePointers.size(); i++)
            {
                bool encounterExecuted;
                searchResultChildren[i] = this->nodePointers[i]->nextActions(executedActions, encounterExecuted);
                for (unsigned int j = 0; j < searchResultChildren[i].size(); j++) // add all the returned executable to actions to searchResultsThis
                    searchResultThis.push_back(searchResultChildren[i][j]);
                if (encounterExecuted)
                    encounterExecutedOut = true;
            }
            return searchResultThis;
            break;

        case OP_UNDEFINED:
        default:
            break;
    }

    return searchResultThis;
}

nodeType_t operatorNode::getNodeType(void)
{
    return ND_OPERATOR;
}

v_action_t operatorNode::getChildrenActions(void)
{
    v_action_t v_action;
    for (unsigned int i = 0; i < this->nodePointers.size(); i++)
    {
        v_action_t v_actionChild;
        v_actionChild = this->nodePointers[i]->getChildrenActions();
        for (unsigned int j = 0; j < v_actionChild.size(); j++)
            v_action.push_back(v_actionChild[j]);
    }
    //   std::cout << "Node returning children actions: ";
    //   for (unsigned int i = 0; i < v_action.size(); i++) 
    //     std::cout << " " << v_action[i] << ";";
    //   std::cout << std::endl;  
    return v_action;
}

void operatorNode::deleteTree(void)
{
    for (std::vector<parseTreeNode*>::iterator it = this->nodePointers.begin(); it != this->nodePointers.end(); it++)
    {
        (*it)->deleteTree();
        delete (*it);
    }
}

parseTreeNode* operatorNode::searchAction(action_t actionIDIn)
{

    for (unsigned int i = 0; i < this->nodePointers.size(); i++)
    {
        parseTreeNode * resultNode = this->nodePointers[i]->searchAction(actionIDIn);
        if (resultNode != NULL)
            return resultNode;
    }
    return NULL;

}

int operatorNode::randomlyShuffleChildren(double shuffleProb)
{

    if ((this->operatorType == OP_ALTERNATIVE) || (this->operatorType == OP_PARALLEL))
    {
        // Generate a random number between 0 and 1
        double randomNumber = rand() / (RAND_MAX + 1.0);

        if (randomNumber <= shuffleProb)
        {

            std::vector <parseTreeNode *> newNodePointers;
            std::vector <int> isIndexAssigned;

            for (unsigned int i = 0; i < this->nodePointers.size(); i++)
                isIndexAssigned.push_back(0);

            for (unsigned int i = this->nodePointers.size(); i > 0; i--)
            {
                // Generate a random number between 1 and i
                int randomIndex = (rand() % i) + 1; // NOTE that this index is between 1 and this->numNodes
                int searchIndex = 0;
                while (randomIndex > 0)
                {
                    if (isIndexAssigned[searchIndex] == 0)
                        randomIndex--;
                    searchIndex++;
                }
                searchIndex--; // Correct the value of searchIndex

                isIndexAssigned[searchIndex] = 1;
                newNodePointers.push_back(this->nodePointers[searchIndex]);
            }
            // Modify to the old pointers to the shuffled new pointers
            this->nodePointers = newNodePointers;
        }
    }

    // Call the recursive function for each one of the children
    for (unsigned int i = 0; i < nodePointers.size(); i++)
        nodePointers[i]->randomlyShuffleChildren(shuffleProb);

    return 1;
}

bool CAlgebraBase::checkFormulaSyntax(const std::string testString)
{
    return true;
}

parseTreeNode *CAlgebraBase::parseFormula(const std::string formulaIn)
{

    parseTreeNode *parseTreeRoot;

    operatorType_t operatorType = OP_UNDEFINED;
    std::string formula = formulaIn;

    for (unsigned int i = 0; i < formula.length(); i++)
    {
        if (formula[i] == '.')
        {
            operatorType = OP_SEQUENTIAL;
            formula = formula.substr(i + 2, formula.rfind(')') - i - 2);
#ifdef PRINT_ALGEBRA_FULL
            printf("SUBFORMULA: %s\n", formula.c_str());
#endif        //#ifdef PRINT_ALGEBRA_FULL

            break;
        }
        if (formula[i] == '+')
        {
            operatorType = OP_ALTERNATIVE;
            formula = formula.substr(i + 2, formula.rfind(')') - i - 2);
#ifdef PRINT_ALGEBRA_FULL
            printf("SUBFORMULA: %s\n", formula.c_str());
#endif        //#ifdef PRINT_ALGEBRA_FULL

            break;
        }
        if (formula[i] == '|')
        {
            operatorType = OP_PARALLEL;
            formula = formula.substr(i + 2, formula.rfind(')') - i - 2);
#ifdef PRINT_ALGEBRA_FULL
            printf("SUBFORMULA: %s\n", formula.c_str());
#endif        //#ifdef PRINT_ALGEBRA_FULL
            break;
        }
        if (formula[i] == 'p')
        {
            operatorType = OP_UNDEFINED;
#ifdef PRINT_ALGEBRA_FULL
            printf("SUBFORMULA:%s\n", formula.c_str());
#endif        //#ifdef PRINT_ALGEBRA_FULL
            formula = formula.substr(i + 1, formula.rfind(')') - i - 2);
#ifdef PRINT_ALGEBRA_FULL
            printf("SUBFORMULA:%s\n", formula.c_str());
#endif        //#ifdef PRINT_ALGEBRA_FULL
            break;
        }
    }

    if (operatorType == OP_UNDEFINED)
    {
        // handle the case when there is only one action in the formula
        action_t actionID = atoll(formula.c_str());

#ifdef PRINT_ALGEBRA_FULL
        COUT_FILE_LINE_MSG("Action ID: [" << actionID << " - " << formula.c_str() << "]");
#endif        //#ifdef PRINT_ALGEBRA_FULL

        bool IDfound = false;
        for (unsigned int i = 0; i < this->actions.size(); i++)
            if (this->actions[i] == actionID)
            {
                IDfound = true;
                break;
            }

        if (IDfound == false)
        {
            std::cout << "Algebra ERROR: Objective [" << actionID << "] ID NOT FOUND" << std::endl;
            return NULL;
        }

        actionNode *actionNodeTmp = new actionNode(actionID);
        parseTreeRoot = (parseTreeNode *) actionNodeTmp;
#ifdef PRINT_ALGEBRA_FULL
        COUT_FILE_LINE_MSG("actionNodeTmp: [" << actionNodeTmp << " - " << formula.c_str() << "]");
#endif        //#ifdef PRINT_ALGEBRA_FULL
    }
    else
    {
        // Handle the case when the subformula is a binding operator

        operatorNode *operatorNodeTmp = new operatorNode;

        operatorNodeTmp->setOperatorType(operatorType);

        int numParanthesis = 0;

        for (unsigned int i = 0; i < formula.length(); i++)
        {
            switch (formula[i])
            {

                case '+':
                case '.':
                case '|':
                    if (numParanthesis == 0)
                    {
                        unsigned int iEnd;
                        int numParanthesisTmp = 0;
                        for (iEnd = i + 1; iEnd < formula.length(); iEnd++)
                        {
                            if (formula[iEnd] == '(')
                                numParanthesisTmp++;
                            if (formula[iEnd] == ')')
                                numParanthesisTmp--;
                            if (numParanthesisTmp == 0)
                                break;
                        }
                        operatorNodeTmp->addNode(parseFormula(formula.substr(i, iEnd - i + 1)));
                    }
                    break;
                case 'p':
                    if (numParanthesis == 0)
                    {
                        unsigned int iEnd;
                        for (iEnd = i + 1; iEnd < formula.length(); iEnd++)
                        {
                            if ((formula[iEnd] == ')') || (formula[iEnd] == ' '))
                                break;
                        }
#ifdef STEVE_FIX
                        parseTreeNode * pTreeNode = parseFormula(formula.substr(i, iEnd - i + 1));
                        if (pTreeNode != 0)
                        {
                            operatorNodeTmp->addNode(pTreeNode);
                        }
                        pTreeNode = 0;
#else //STEVE_FIX
                        operatorNodeTmp->addNode(parseFormula(formula.substr(i, iEnd - i + 1)));
#endif //STEVE_FIX
                    }
                    break;

                case '(':
                    numParanthesis++;
                    break;

                case ')':
                    numParanthesis--;
                    break;

                default:
                    break;
            }
        }

        // Set the parent pointer of all the children
        for (int i = 0; i < operatorNodeTmp->getNumNodes(); i++)
        {
            parseTreeNode *childrenNode = operatorNodeTmp->getNodePointer(i);
            childrenNode->parent = operatorNodeTmp;
        }

        // Return the address of this node
        parseTreeRoot = (parseTreeNode *) operatorNodeTmp;

    }

    return parseTreeRoot;
}

void CAlgebraBase::initPredsRec(parseTreeNode *ptRoot)
{
  
    if (ptRoot->getNodeType() == ND_OPERATOR)
    {
        // Get all the children actions of all the children nodes and store in the data structure below
        std::vector <v_action_t> childrenActionsChildren;
        operatorNode *ptRootOpr = (operatorNode *) ptRoot;
        if (ptRootOpr->getOperatorType() == OP_SEQUENTIAL)
        {
            for (int i = 0; i < ptRootOpr->getNumNodes(); i++)
            {
                parseTreeNode *childNode = ptRootOpr->getNodePointer(i);
                childrenActionsChildren.push_back(childNode->getChildrenActions());
//                std::cout << "acquired children actions:";
//                for (unsigned int j = 0; j < childrenActionsChildren[i].size(); j++)
//                    std::cout << " " << childrenActionsChildren[i][j] << ";";
//                std::cout << std::endl;
            }
        }

        // Initialize the predecessors for each child node
        if (childrenActionsChildren.size() > 0)
        { // Check whether there is at least two children of this node
            for (unsigned int i = 1; i < childrenActionsChildren.size(); i++)
            {
                for (unsigned int j = 0; j < childrenActionsChildren[i].size(); j++)
                {
                    // find the element with action ID indicated in childrenActionsChildren[i][j]
                    int actionIndex = findActionIndexviaActionID(childrenActionsChildren[i][j]);
                    // add all the actions in childrenActionsChildren[k] with all k < i into preds[actionIndex]
                    if (actionIndex >= 0)
                    {
                        for (unsigned int k = 0; k < i; k++)
                        {
                            for (unsigned int l = 0; l < childrenActionsChildren[k].size(); l++)
                            {
                                bool actionFound = false;
                                // Check whether childrenActionsChildren[k][l] is in the preds list
                                for (unsigned int m = 0; m < preds[actionIndex].size(); m++)
                                {
                                    if (preds[actionIndex][m] == childrenActionsChildren[k][l])
                                        actionFound = true;
                                }
                                if (!actionFound)
                                    preds[actionIndex].push_back(childrenActionsChildren[k][l]);
                            }
                        }
                    }
                    else
                    {
                        CERR_FILE_LINE_MSG("ERROR:: could not find actionIndex for [" << childrenActionsChildren[i][j] << "]")
                    }
                }
            }
        }

        // Recursively call yourself for each child node
        for (int i = 0; i < ptRootOpr->getNumNodes(); i++)
        {
            parseTreeNode *childNode = ptRootOpr->getNodePointer(i);
            initPredsRec(childNode);
        }

    }
}

int CAlgebraBase::findActionIndexviaActionID(action_t actionID)
{
    for (unsigned int i = 0; i < actions.size(); i++)
        if (actions[i] == actionID)
            return i;
    return -1;
}

int CAlgebraBase::randomlyShuffleTree(double shuffleProb)
{
    return this->parseTreeRoot->randomlyShuffleChildren(shuffleProb);
}

CAlgebra::CAlgebra(void)
{
    parseTreeRoot = NULL;
    return;
}

bool CAlgebra::initAtomicObjectives(const v_action_t &atomicObjectiveIDs)
{
    // free all the data structures 
    this->actions.clear();
    for (unsigned int i = 0; i < this->preds.size(); i++)
        this->preds[i].clear();
    this->preds.clear();
    if (this->parseTreeRoot)
        this->parseTreeRoot->deleteTree();
    this->parseTreeRoot = NULL;

    // Initialize the atomic objectives
    if (atomicObjectiveIDs.size() == 0)
        return false;
    this->actions = atomicObjectiveIDs;
    return true;
}

bool CAlgebra::initAlgebraString(const std::string stringIn)
{
    // Check the formula for syntax errors
    printf("\nAlgebraString:: %s\n\n", stringIn.c_str());
    if (checkFormulaSyntax(stringIn) == false)
    {
        return false;
    }

    // Parse the algebra std::string
    this->parseTreeRoot = parseFormula(stringIn);
    if (this->parseTreeRoot == NULL)
        return false;
    this->parseTreeRoot->parent = NULL;


    // Initialize the predecessors 
    for (unsigned int i = 0; i < actions.size(); i++)
    {
        v_action_t empty_action_list;
        preds.push_back(empty_action_list);
    }

    initPredsRec(this->parseTreeRoot);

    //cout << "Predecessors::" << std::endl;
    //for (unsigned int i = 0; i < preds.size(); i++) {
    //  std::cout << "Action [" << actions[i] << "] preds:";
    //  for (unsigned int j = 0; j < preds[i].size (); j++)
    //    std::cout << " " << preds[i][j] << ";";
    //  //cout << std::endl;
    //}
    //cout << std::endl;

    return true;
}

void CAlgebra::searchNext(const v_action_t &executedAtomicObjectives, v_action_t& nextAtomicObjectives)
{
    bool encounterExecuted;
    nextAtomicObjectives = this->parseTreeRoot->nextActions(executedAtomicObjectives, encounterExecuted);

}

v_action_t CAlgebra::searchPred(const v_action_t &executedAtomicObjectives, int AtomicObjectiveIn)
{

    v_action_t v_action;

    int actionIndex = findActionIndexviaActionID(AtomicObjectiveIn);

    for (unsigned int i = 0; i < preds[actionIndex].size(); i++)
        for (unsigned int j = 0; j < executedAtomicObjectives.size(); j++)
            if (preds[actionIndex][i] == executedAtomicObjectives[j])
                v_action.push_back(executedAtomicObjectives[j]);

    return v_action;
}

}; //namespace log
}; //namespace common
}; //namespace uxas
