/**
* TODO
* 1. Merge with OpenUxAS
* 2. Reduce visibility of global var
* 3. Decide what contained to store in (map for syntax, vector for prereq)
* 4. Store all information in previously defined structure
* 5. All error checking
*     - Add class for digit maybe, to help in error checking?
* 6. Finish all other TODOs
*/

#include <vector>
#include <string>
#include <queue>
#include <map>
#include <iostream>
#include "UxAS_LexicalAnalyzer.h"

namespace uxas
{
    namespace common
    {
        namespace utilities
        {
            //Enums
            enum TokenClass {OPERATOR = 0, OPERAND = 1, TIME = 2, UNKNOWN = 100};
            enum Token {ALTERNATIVE = 10, SEQUENTIAL = 11, PARALLEL = 12, RELATIVE = 13,
                ABSOLUTE = 14, TILDE = 15, COMMA = 16, BRACKET_LEFT = 17,
                BRACKET_RIGHT = 18, PAREN_LEFT = 19, PAREN_RIGHT = 20, TASK = 21, UNDEFINED = 200};

            //Constructor
            Lex::Lex(){};

            //clone the map
            std::shared_ptr<std::map<int, std::array<std::vector<std::vector<int> >, 2> > > Lex::cloneTasksToTime(){               
                return (std::shared_ptr<std::map<int, std::array<std::vector<std::vector<int> >, 2> > >(new std::map<int, std::array<std::vector<std::vector<int> >, 2> >(tasksToTime)));
            }

            /**
             * Init variables and begin recursive descent
             * @param tmpAlgebraString //string: unexpanded algebra string
             */
            std::map<int, std::array<std::vector<std::vector<int> >, 2>> Lex :: parse(std::string tmpAlgebraString) {
                /**
                 * TODO
                 * 1. Reduce level of initialization
                 */
                //Init var
                algebraString = tmpAlgebraString;
                lexeme = "";
                pos = -1;
                timing_pos = 0;
                timingFlags.at(0) = 0;
                prereq_paren_count = 0;
                add_all_paren_count = 0;

                //Start lex processing
                rDec();
                //Return map here
                return tasksToTime;
            }

            /**
             * A recursive descent parser: processes the lex and checks for errors
             */
            void Lex :: rDec() {
                //While not EOF
                if (lex() != 0) {
                    //Recursively call rDec in this section. It should never reach else until EOF.

                    /**
                     * ERROR CHECKING GOES HERE:
                     * 1. Tilde or dot is in wrong format; ~(p1 p2) or ~((set1)(set2)) are fine
                     *    same for dot (require two sets)
                     * 2. Error if symbol not number and defined character
                     * 3. If first thing in file is not operator then invalidwhile (lex()) {
                     * 4. If carat or parens are missing then error
                     * 5. If comma is missing
                     * 6. If time does not have both t1 and t2
                     * 7. If the times are not unsigned (check if less than 0)
                     * 8. All parens
                     */
                }
                //When rDec is finally done, parse needs to return the map
            }
            /**
             * Lexical analysis of each character token
             * @return //The character token type
             */
            int Lex :: lex() {
                //Reset lexeme
                lexeme = "";

                //Get next character and add it to lexeme
                if (getNonBlank() == 0) {
                    return 0;
                }
                lookup(nextChar);
                addChar(nextChar);

                //Check class of nextChar to process timing information
                switch(charClass) {
                    case OPERAND:
                        //Get task id as int
                        lexeme = "";
                        while (!isspace(nextChar)) {
                            getNonBlank();
                            addChar(nextChar);
                        }
                        taskId = std::stoi(lexeme);

                        //If prereq flags are set
                        if (set_prereq) {
                            if (add_all_prereq) {
                                storePrereqInfo(taskId);
                                prereq_q.push(taskId);
                            }
                            else {
                                storePrereqInfo(taskId);
                                prereq_op_q.pop();
                                prereq_v.clear();
                                prereq_v.push_back(taskId);
                            }
                        }
                        //If the timing flag is set
                        if (timingFlags.at(0)) {
                            storeTimeInfo(std::stoi(lexeme));
                        }
                        break;
                    case OPERATOR:
                        //Check operator type to set prerequisite tasks
                        if((nextToken == SEQUENTIAL) || (nextToken == TILDE)) {
                            //Check if valid syntax and set flag to process task prerequisites
                            isValidSyntax();
                            set_prereq = true;
                            prereq_op_q.push(nextToken);
                        }
                        else if ((nextToken == PARALLEL) || (nextToken == ALTERNATIVE)) {
                            //If the prerequisite flag is set, then set the add all flag
                            if (set_prereq) {
                                add_all_prereq = true;
                            }
                        }
                        break;
                    case TIME:
                        //If relative or absolute, create timing flag
                        if ((nextToken == RELATIVE) || (nextToken == ABSOLUTE)) {
                            //If the end of the timing space is reached, reset and exit
                            if (timing_pos == pos) {
                                timingFlags.at(0) = 0;
                                while (getNonBlank() != ']');
                            }
                                //Else set the timing flags and start traversing the space
                            else {
                                setTimingFlags();
                            }
                        }
                        break;
                    case UNKNOWN:
                        //Ignore nested loops when processing timing
                        if (timingFlags.at(0) && (nextToken == PAREN_LEFT)) {
                            skipToSectionEnd(true);
                        }
                        /**
                         * Check to see if prereq flags need to be unset
                         * Will init flags if not init
                         */
                        if (set_prereq) {
                            if (deactivateFlagCheck(&prereq_paren_count)) {
                                set_prereq = false;
                                prereq_v.clear();
                                while(!prereq_q.empty()) {
                                    prereq_q.pop();
                                }
                                while(!prereq_op_q.empty()) {
                                    prereq_op_q.pop();
                                }
                            }
                        }
                        if (add_all_prereq) {
                            if (deactivateFlagCheck(&add_all_paren_count)) {
                                add_all_prereq = false;
                                prereq_v = prereqToVector(prereq_q);
                                prereq_op_q.pop();
                            }
                        }
                        break;
                    default:
                        break;
                }
                return nextToken;
            }
            /**
             * Determine the token type and class of the next character
             * @param ch //char: the character to check
             * @return //int: the character token's class
             */
            int Lex :: lookup(char ch) {
                switch(ch) {
                    case '+':
                        nextToken = ALTERNATIVE;
                        charClass = OPERATOR;
                        break;
                    case '.':
                        nextToken = SEQUENTIAL;
                        charClass = OPERATOR;
                        break;
                    case '|':
                        nextToken = PARALLEL;
                        charClass = OPERATOR;
                        break;
                    case '~':
                        nextToken = TILDE;
                        charClass = OPERATOR;
                        break;
                    case '(':
                        nextToken = PAREN_LEFT;
                        charClass = UNKNOWN;
                        break;
                    case ')':
                        nextToken = PAREN_RIGHT;
                        charClass = UNKNOWN;
                        break;
                    case '[':
                        nextToken = BRACKET_LEFT;
                        charClass = UNKNOWN;
                        break;
                    case ']':
                        nextToken = BRACKET_RIGHT;
                        charClass = UNKNOWN;
                        break;
                    case ',':
                        nextToken = COMMA;
                        charClass = UNKNOWN;
                        break;
                    case '-':
                        nextToken = RELATIVE;
                        charClass = TIME;
                        break;
                    case '_':
                        nextToken = ABSOLUTE;
                        charClass = TIME;
                        break;
                    case 'p':
                        nextToken = TASK;
                        charClass = OPERAND;
                        break;
                    default:
                        nextToken = UNDEFINED;
                        charClass = UNKNOWN;
                        break;
                }

                return charClass;
            }
            /**
             * Get the next non-whitespace character
             * @return //char: the next non-whitespace character
             */
            char Lex :: getNonBlank() {
                do {
                    if (++pos < algebraString.length()) {
                        nextChar = (char) algebraString.at(pos);
                    }
                    else {
                        return 0; //EOF
                    }
                }
                while(isspace(nextChar));
                return nextChar;
            }
            /**
             * Append a character to the lexeme string
             * @param ch //char: character to append
             */
            void Lex :: addChar(char ch) {
                lexeme.push_back(ch);
            }
            /**
             * Collect the timing data to append to task nodes
             */
            void Lex :: setTimingFlags() {
                /**
                 * TODO
                 * 1. EOF processing
                 * 2. T1/T2 Error checking
                 */
                //Set relative or absolute
                timingFlags.at(0) = nextToken;

                //Save timing information and position of timing op
                timing_pos = pos;
                std::string t1, t2;
                char tmp_char;
                while (((tmp_char = getNonBlank()) != ',') && (tmp_char != 0)) {
                    t1.push_back(tmp_char);
                }
                while (((tmp_char = getNonBlank()) != ']') && (tmp_char != 0)) {
                    t2.push_back(tmp_char);
                }
                if (tmp_char == 0) {
                    //Error: EOF. Should never reach EOF here.
                }
                timingFlags.at(1) = std::stoi(t1);
                timingFlags.at(2) = std::stoi(t2);

                //Set pos to beginning of this timing section
                skipToSectionEnd(false); //False to process string backwards
            }
            /**
             * Check if a character is an operator
             * @param ch //char: character to check
             * @return //bool: if it is an operator, set true
             */
            bool isOperator(char ch) {
                //Will fall through to the last two cases
                switch (ch) {
                    case '+':
                    case '|':
                    case '.':
                    case '~':
                        return true;
                    default:
                        return false;
                }
            }
            /**
             * Confirm that the syntax of the dot or tilde operator is valid
             * @return //bool: if syntax valid, set true
             */
            bool Lex :: isValidSyntax() {
                /**
                 * TODO
                 * 1. Change paren count to start at 1, look for nested loops (skip nested?)
                 * 2. If nested dot or tilde, save pos and process those next
                 * 3. EOF processing
                 * 3. Send errors
                 */
                //Set pos to be after dot or tilde operator
                while(getNonBlank() != '(');
                getNonBlank();

                //Var
                bool end = false;
                int position_count = 0;
                char tmp_char;

                //Check that the syntax follows OPERATOR(position_1 position_2)
                do {
                    //Keep iterating until the operator section is over
                    if ((tmp_char = getNonBlank()) != 0) {
                        switch (tmp_char) {
                            case '(': //Collection of tasks not preceded by an operator
                                position_count++;
                                skipToSectionEnd(true);
                                break;
                            case ')': //End of operator section
                                end = true;
                                break;
                            case 'p': //Task that is not within any parens
                                position_count++;
                                break;
                            default:
                                break;
                        }
                        //Nested operator encountered. Skip to end of its section.
                        if (isOperator(tmp_char)) {
                            getNonBlank();
                            position_count++;
                            skipToSectionEnd(true);
                        }
                    }
                    else {
                        //Error, EOF. Should never hit here.
                        return false;
                    }
                } while(!end);

                if (position_count > 2) {
                    //Error. More than the two positions allowed occupied.
                    return false;
                }
                return true;
            }
            /**
             * Skip from a beginning paren to its corresponding ending paren
             * @param goForward //bool: if processed from left to right, set true
             */
            void Lex :: skipToSectionEnd(bool goForward) {
                int paren_count = 1; //First paren is always skipped
                //Process the string in a forward direction
                if (goForward) {
                    do {
                        if (algebraString.at(++pos) == '(') {
                            paren_count++;
                        }
                        else if (algebraString.at(pos) == ')') {
                            paren_count--;
                        }
                    } while(paren_count != 0);
                }
                    //Process the string in a backwards direction
                else {
                    do {
                        if (algebraString.at(--pos) == ')') {
                            paren_count++;
                        }
                        else if (algebraString.at(pos) == '(') {
                            paren_count--;
                        }
                    } while(paren_count != 0);
                }
            }
            /**
             * Check whether to deactivate a prerequisite flag
             * @param counter //int*: pointer to global paren counter for flag
             * @return //bool: what value the flag should be set to this round
             */
            bool Lex :: deactivateFlagCheck(int *counter) {
                //Keep track of the parens to know when to deactivate the flag
                if (nextToken == PAREN_LEFT) {
                    (*counter)++;
                }
                else if (nextToken == PAREN_RIGHT) {
                    (*counter)--;
                }
                //Deactivate the flag
                return (*counter == 0);
            }

            std::vector<int> Lex :: prereqToVector(std::queue<int> tmp_queue) {
                std::vector<int> tmp_vector;
                while (!tmp_queue.empty()) {
                    tmp_vector.push_back(tmp_queue.front());
                    tmp_queue.pop();
                }
                return tmp_vector;
            }

            std::vector<int> Lex :: opToVector(int frontValue, int size) {
                std::vector<int> tmp_vector;
                for (int i = 0; i < size; i++) {
                    tmp_vector.push_back(frontValue);
                }
                return tmp_vector;
            }

            void Lex :: storeTimeInfo(int taskId) {
                std::vector<int> timing_op;
                std::vector<std::vector<int> > timing;
                std::array<std::vector<std::vector<int> >,2> time_prereq_arr;

                timing.push_back(timingFlags);
                timing.push_back(timing_op);

                //Prereq info is already added for this task
                if (!tasksToTime.at(taskId)[1].empty()) {
                    time_prereq_arr = tasksToTime.at(taskId);
                    time_prereq_arr[0] = timing;
                    tasksToTime.at(taskId) = time_prereq_arr;
                }
                    //No prereq info for this task
                else {
                    time_prereq_arr[0] = timing;
                    auto time_pair = std::make_pair(taskId,time_prereq_arr);
                    tasksToTime.insert(time_pair);
                }
            };

            void Lex :: storePrereqInfo(int taskId) {
                std::vector<int> prereq_op_v = opToVector(prereq_op_q.front(), prereq_v.size());
                std::vector<std::vector<int> > prereq;
                std::array<std::vector<std::vector<int> >,2> time_prereq_arr;

                prereq.push_back(prereq_v);
                prereq.push_back(prereq_op_v);

                //Check if timing info has already been added (should be false)
                if (!tasksToTime.at(taskId)[0].empty()) {
                    time_prereq_arr = tasksToTime.at(taskId);
                    time_prereq_arr[1] = prereq;
                    tasksToTime.at(taskId) = time_prereq_arr;
                }
                else {
                    time_prereq_arr[1] = prereq;
                    auto prereq_pair = std::make_pair(taskId,time_prereq_arr);
                    tasksToTime.insert(prereq_pair);
                }
            }
        };
    };
};
