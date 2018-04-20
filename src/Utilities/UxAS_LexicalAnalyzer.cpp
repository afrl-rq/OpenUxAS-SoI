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

            /**
             * Init variables and begin recursive descent
             * @param tmpAlgebraString //string: unexpanded algebra string
             */
            void Lex :: parse(std::string tmpAlgebraString, std::shared_ptr<std::map<int, std::array<std::vector<std::vector<int> >, 2> > > m_map) {
                std::cout << "parse has run" << std::endl;
                /**
                 * TODO
                 * 1. Reduce level of initialization
                 */
                //Init var
                std::cout << "test" << std::endl;
                algebraString = tmpAlgebraString;
                lexeme = "";
                pos = 0;
                timing_pos = 0;
                timingFlags.at(0) = 0;
                prereq_paren_count = 0;
                add_all_paren_count = 0;
                tasksToTime = m_map;
                placeholder_arr = {};

                //Start lex processing
                std::cout << "SetF Test Start of rDec()" << std::endl;
                rDec();
            }

            /**
             * A recursive descent parser: processes the lex and checks for errors
             */
            void Lex :: rDec() {
                std::cout << "rDec" << std::endl;

                //While not EOF
                while (lex() != 0) {
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
                std::cout << "lex" << std::endl;

                //Reset lexeme
                int err_char;
                lexeme = "";

                //Get next character and add it to lexeme
                if (getNonBlank() == 0) {
                    std::cout << "lex_branch_EOF_1" << std::endl;
                    return 0;
                }
                lookup(nextChar);
                addChar(nextChar);

                //Check class of nextChar to process timing information
                switch(charClass) {
                    case OPERAND:
                        std::cout << "lex_branch_OPERAND" << std::endl;
                        //Get task id as int
                        lexeme = "";
                        char tmp_char;
                        while (((tmp_char = getNonBlank()) != 0) && isdigit(tmp_char)) {
                            addChar(tmp_char);
                        }
                        pos--;
                        std::cout << "taskId: " << lexeme << std::endl;
                        taskId = std::stoi(lexeme);

                        //Check if the task is in the map. If not, add a placeholder.
                        if (tasksToTime->find(taskId) == tasksToTime->end()) {
                            auto placeholder = std::make_pair(taskId, placeholder_arr);
                            tasksToTime->insert(placeholder);
                        }

                        //If prereq flags are set
                        if (set_prereq) {
                            std::cout << "lex_branch_prereqTrue" << std::endl;
                            if (add_all_prereq) {
                                std::cout << "lex_branch_OP_prereq-True_addAll-True" << std::endl;
                                storePrereqInfo(taskId);
                                prereq_q.push(taskId);
                            }
                            else {
                                std::cout << "lex_branch_OP_prereq-True_addAll-False" << std::endl;
                                storePrereqInfo(taskId);
                                prereq_op_q.pop();
                                prereq_v.clear();
                                prereq_v.push_back(taskId);
                            }
                        }
                        //If the timing flag is set
                        if (timingFlags.at(0)) {
                            std::cout << "lex_branch_timingFlag-True" << std::endl;
                            storeTimeInfo(taskId);
                        }
                        break;
                    case OPERATOR:
                        std::cout << "lex_branch_OPERATOR" << std::endl;
                        //Check operator type to set prerequisite tasks
                        if((nextToken == SEQUENTIAL) || (nextToken == TILDE)) {
                            //Check if valid syntax and set flag to process task prerequisites
                            std::cout << "lex_branch_SEQ-TILDE" << std::endl;
                            set_prereq = true;
                            prereq_op_q.push(nextToken);
                        }
                        else if ((nextToken == PARALLEL) || (nextToken == ALTERNATIVE)) {
                            std::cout << "lex_branch_PARA-ALT" << std::endl;
                            //If the prerequisite flag is set, then set the add all flag
                            if (set_prereq) {
                                add_all_prereq = true;
                            }
                        }
                        break;
                    case TIME:
                        std::cout << "lex_branch_TIME" << std::endl;
                        //If relative or absolute, create timing flag
                        if ((nextToken == RELATIVE) || (nextToken == ABSOLUTE)) {
                            std::cout << "lex_branch_REL-ABS" << std::endl;
                            //If the end of the timing space is reached, reset and exit
                            if (timing_pos == pos) {
                                std::cout << "lex_branch_timing-over" << std::endl;
                                timingFlags.at(0) = 0;
                                while (((err_char = getNonBlank()) != ']') && (err_char != 0));
                                if (err_char == 0) {
                                    std::cout << "lex_branch_EOF_3" << std::endl;
                                    return 0;
                                }
                            }
                            //Else set the timing flags and start traversing the space
                            else {
                                std::cout << "lex_branch_setTimingFlags" << std::endl;
                                setTimingFlags();
                            }
                        }
                        break;
                    case UNKNOWN:
                        std::cout << "lex_branch_UNKNOWN" << std::endl;
                        //Ignore nested loops when processing timing
                        if (timingFlags.at(0) && (nextToken == PAREN_LEFT)) {
                            std::cout << "lex_branch_timing_paren-left" << std::endl;
                            skipToSectionEnd(true);
                        }
                        /**
                         * Check to see if prereq flags need to be unset
                         * Will init flags if not init
                         */
                        if (set_prereq) {
                            std::cout << "lex_branch_UNKN_prereq-True" << std::endl;
                            if (deactivateFlagCheck(&prereq_paren_count)) {
                                set_prereq = false;
                                prereq_v.clear();
                                while(!prereq_q.empty()) {
                                    prereq_q.pop();
                                }
                            }
                        }
                        if (add_all_prereq) {
                            std::cout << "lex_branch_UNKN_addAdd-True" << std::endl;
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
                std::cout << "lookup" << std::endl;

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
                    if (pos < algebraString.length()) {
                        nextChar = (char) algebraString.at(pos++);
                    }
                    else {
                        std::cout << "getNonBlank: END" << std::endl;
                        return 0; //EOF
                    }
                }
                while(isspace(nextChar));

                std::cout << "getNonBlank: " << nextChar << std::endl;
                return nextChar;
            }
            /**
             * Append a character to the lexeme string
             * @param ch //char: character to append
             */
            void Lex :: addChar(char ch) {
                std::cout << "addChar" << std::endl;
                lexeme.push_back(ch);
            }
            /**
             * Collect the timing data to append to task nodes
             */
            void Lex :: setTimingFlags() {
                std::cout << "setTimingFlags" << std::endl;

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
                while (((tmp_char = getNonBlank()) != '[') && (tmp_char != 0));
                while (((tmp_char = getNonBlank()) != ',') && (tmp_char != 0)) {
                    t1.push_back(tmp_char);
                }
                while (((tmp_char = getNonBlank()) != ']') && (tmp_char != 0)) {
                    t2.push_back(tmp_char);
                }
                if (tmp_char == 0) {
                    //Error: EOF. Should never reach EOF here.
                    std::cout << "setTiming_EOF" << std::endl;
                }
                std::cout << t1 << std::endl;
                timingFlags.at(1) = std::stoi(t1);
                std::cout << t2 << std::endl;
                timingFlags.at(2) = std::stoi(t2);

                //Set pos to beginning of this timing section
                pos = timing_pos - 1;
                skipToSectionEnd(false); //False to process string backwards
            }
            /**
             * Check if a character is an operator
             * @param ch //char: character to check
             * @return //bool: if it is an operator, set true
             */
            bool isOperator(char ch) {
                std::cout << "isOperator" << std::endl;

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
             * Skip from a beginning paren to its corresponding ending paren
             * @param goForward //bool: if processed from left to right, set true
             */
            void Lex :: skipToSectionEnd(bool goForward) {
                std::cout << "skipToSectionEnd" << std::endl;
                int paren_count;

                //Process the string in a forward direction
                if (goForward) {
                    paren_count = 1; //First paren is always skipped
                    do {
                        if (algebraString.at(++pos) == '(') {
                            paren_count++;
                        }
                        else if (algebraString.at(pos) == ')') {
                            paren_count--;
                        }
                    } while((paren_count != 0) && (pos < algebraString.length()));
                }
                    //Process the string in a backwards direction
                else {
                    paren_count = 0;
                    do {
                        if (algebraString.at(--pos) == ')') {
                            paren_count++;
                        }
                        else if (algebraString.at(pos) == '(') {
                            paren_count--;
                        }
                    } while((paren_count != 0) && (pos < algebraString.length()) && (pos > 0));
                    pos++;
                }
                //Wrong # of parens
                if ((pos >= algebraString.length()) && (paren_count != 0)) {
                    std::cout << "skipToSectionEnd_EOF" << std::endl;
                    //Error. Hit EOF with the wrong number of parens.
                }
            }
            /**
             * Check whether to deactivate a prerequisite flag
             * @param counter //int*: pointer to global paren counter for flag
             * @return //bool: what value the flag should be set to this round
             */
            bool Lex :: deactivateFlagCheck(int *counter) {
                std::cout << "deactivateFlagCheck" << std::endl;
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
                std::cout << "prereqToVector" << std::endl;
                std::vector<int> tmp_vector;
                while (!tmp_queue.empty()) {
                    tmp_vector.push_back(tmp_queue.front());
                    tmp_queue.pop();
                }
                return tmp_vector;
            }

            std::vector<int> Lex :: opToVector(int frontValue, int size) {
                std::cout << "opToVector" << std::endl;

                std::vector<int> tmp_vector;
                for (int i = 0; i < size; i++) {
                    tmp_vector.push_back(frontValue);
                }
                return tmp_vector;
            }

            void Lex :: storeTimeInfo(int taskId) {
                std::cout << "StoreTimeInfo" << std::endl;

                std::vector<int> timing_op;
                std::vector<std::vector<int> > timing;
                std::array<std::vector<std::vector<int> >,2> time_prereq_arr;

                timing.push_back(timingFlags);
                timing.push_back(timing_op);

                //Add to map
                time_prereq_arr = tasksToTime->at(taskId);
                time_prereq_arr[0] = timing;
                tasksToTime->at(taskId) = time_prereq_arr;
            };

            void Lex :: storePrereqInfo(int taskId) {
                std::cout << "storePrereqInfo" << std::endl;

                std::vector<int> prereq_op_v = opToVector(prereq_op_q.front(), prereq_v.size());
                std::vector<std::vector<int> > prereq;
                std::array<std::vector<std::vector<int> >,2> time_prereq_arr;

                prereq.push_back(prereq_v);
                prereq.push_back(prereq_op_v);

                //Add to map
                time_prereq_arr = tasksToTime->at(taskId);
                time_prereq_arr[1] = prereq;
                tasksToTime->at(taskId) = time_prereq_arr;
            }
        };
    };
};
