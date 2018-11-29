// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   DbHelper.h
 * Author: jon
 *
 * Created on October 23, 2018, 2:08 PM
 */

#include "LoggedMessage.h"
#include <vector>
#include <string>
#include <SQLiteCpp/Database.h>
#include <SQLiteCpp/SQLiteCpp.h>
#include "stdUniquePtr.h"
#include <fstream>
#include <memory>

#ifndef DBHELPER_H
#define DBHELPER_H

class DbHelper{
public:
    DbHelper(const std::string& dbLogPath) : dbLogPath(dbLogPath)
    {
    }

    DbHelper(const DbHelper& orig) {
    }

    ~DbHelper() {
    }
    
    std::vector<std::shared_ptr<LoggedMessage>> GetLoggedMessagesByDescriptor(std::string descriptor){
        return getMessagesWithDescriptor(descriptor);
    }

private:
    std::string dbLogPath;
private:
    //queries the Db with the message's descriptor and returns LoggedMessages
    std::vector<std::shared_ptr<LoggedMessage>> getMessagesWithDescriptor(std::string descriptor)
    {
        std::string queryString = "SELECT * FROM msg WHERE descriptor = \"" + descriptor +"\"";
        return getMessagesWithSqlString(queryString);
    }

    //queries the db with the sql string and returns LoggedMessages
    std::vector<std::shared_ptr<LoggedMessage>> getMessagesWithSqlString(std::string queryString)
    {
        std::vector<std::shared_ptr<LoggedMessage>> loggedMessages;
        std::ifstream dbFile(dbLogPath);
        if (dbFile.is_open())
        {
            // file is there, now reopen in sqlite
            dbFile.close();
            auto m_db = uxas::stduxas::make_unique<SQLite::Database>(dbLogPath, SQLITE_OPEN_READONLY);
            SQLite::Statement selectStatements(*(m_db.get()), queryString);
            while (selectStatements.executeStep())
            {
                int id;
                int64_t time_ms;
                std::string descriptor;
                std::string groupID;
                int entityID;
                int serviceID; 
                std::string xml;

                for (int i = 0; i < selectStatements.getColumnCount(); i++)
                {
                    std::string columnName = selectStatements.getColumnName(i);
                    if(columnName == "id" ){
                        id = selectStatements.getColumn(i).getInt();
                    }else if(columnName == "time_ms"){
                        time_ms = selectStatements.getColumn(i).getInt64();
                    }else if(columnName == "descriptor"){
                        descriptor = std::string(selectStatements.getColumn(i).getText());
                    }else if(columnName == "groupID"){
                        groupID = std::string(selectStatements.getColumn(i).getText());
                    }else if(columnName == "entityID"){
                        entityID = selectStatements.getColumn(i).getInt();
                    }else if (columnName == "serviceID"){
                        serviceID = selectStatements.getColumn(i).getInt();
                    } else if(columnName == "xml"){
                        xml = std::string(selectStatements.getColumn(i).getText());
                    }
                }
                //make newMEssage a shared pointer
                auto newMessage = std::make_shared<LoggedMessage>(id, time_ms, descriptor, groupID, entityID, serviceID, xml);
                //auto newMessage = new LoggedMessage(id, time_ms, descriptor, groupID, entityID, serviceID, xml);                
                loggedMessages.push_back(newMessage);
            }
        }
        return loggedMessages;
    }
    

};

#endif /* DBHELPER_H */

