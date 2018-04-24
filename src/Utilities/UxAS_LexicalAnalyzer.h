//
// Created by angela on 3/30/18.
//

#ifndef TEST_LEX_H
#define TEST_LEX_H

#include <queue>
#include <map>
#include <memory>

namespace uxas
{
    namespace common
    {
        namespace utilities
        {
            class Lex {
            public:
                Lex();
                virtual ~Lex(){ };
                void parse(std::string algebraString);//, std::map<int, std::array<std::vector<std::vector<int> >, 2> > * m_map, int * testingTemp);
                std::map<int, std::array<std::vector<std::vector<int> >, 2> > * tasksToTime;
            protected:
                std::array<std::vector<std::vector<int> >,2> placeholder_arr;
                int charClass;
                std::string lexeme;
                std::string algebraString;
                char nextChar;
                int nextToken;
                int taskId;
                bool set_prereq = false, add_all_prereq = false;
                int pos, timing_pos;
                int prereq_paren_count, add_all_paren_count;

                std::vector<int> timingFlags = {0,0,0};
                std::vector<int> prereq_v;
                std::queue<int> prereq_q;
                std::queue<int> prereq_op_q;
            private:
                void rDec();
                char getNonBlank();
                void addChar(char ch);
                int lex();
                int lookup(char ch);
                void setTimingFlags();
                void skipToSectionEnd(bool isBackward);
                bool deactivateFlagCheck(int *counter);
                std::vector<int> prereqToVector(std::queue<int> tmp_queue);
                std::vector<int> opToVector(int frontValue, int size);
                void storeTimeInfo(int taskId);
                void storePrereqInfo(int taskId);
            };
        };
    };
};

#endif //TEST_LEX_H
