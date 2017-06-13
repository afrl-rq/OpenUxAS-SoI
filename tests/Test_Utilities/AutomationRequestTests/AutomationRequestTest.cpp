#include "gtest/gtest.h"
#include "GtestuxastestserviceServiceManagerStartAndRun.h"

#include "afrl/cmasi/AutomationResponse.h"
#include "afrl/cmasi/MissionCommand.h"
#include "afrl/cmasi/Waypoint.h"

// TEST(Parameter01,Parameter02) - Google Test Macro
// Parameter01: "test case" (name of collection of tests)
// Parameter02: "test" (name of test)
TEST(AutomationRequestTest, Test01_GoodRequest)
{
    //**************************************************************************
    //  INITIALIZE TEST SETUP
    //**************************************************************************
    // duration_s - number of second to run UxAS
    uint32_t duration_s{3};
    // testPath - relative path to the directory containing configration and othe test files
    std::string testPath("../tests/Test_Utilities/AutomationRequestTests/");
    // uxasConfigurationFile - path and file name of the UxAS configuration file
    std::string uxasConfigurationFile = testPath + "cfg_AutomationRequest_Test01.xml";
    // outputPath - path for saving output files
    std::string outputPath = testPath + "output/";
    // outputPath - path for saving log files
    std::string logPath = outputPath + "log/";
    // initialze the UxAS loggers
    gtestuxascommonLogManagerInitialize(logPath);
    // savedMessagesPath - the path and file name of the saved messages database are returned in this variable
    std::string savedMessagesPath;

    //**************************************************************************
    //  RUN THE TEST
    //**************************************************************************
    gtestuxastestserviceServiceManagerStartAndRun(duration_s,uxasConfigurationFile, outputPath, savedMessagesPath);

    //*************************************************************************
    //  CHECK RESULTS
    //*************************************************************************
    // use GoogleTest macros to perform tests on the output
    // CountMessagesInLogDb(savedMessagesPath,messageDescription) - queries the saved messages database 
    // and returns the number of messages with the given "description"
    //   - savedMessagesPath - the path and file name of the saved messages database
    //   - messageDescription - message description of messages to count

    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.uxnative.StartupComplete")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.cmasi.AirVehicleConfiguration")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.cmasi.AirVehicleState")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.cmasi.AreaSearchTask")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.cmasi.AutomationRequest")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.cmasi.AutomationResponse")));
    EXPECT_EQ(2,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.cmasi.KeepOutZone")));
    EXPECT_EQ(2,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.cmasi.LineSearchTask")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.cmasi.OperatingRegion")));
    EXPECT_EQ(4,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.cmasi.ServiceStatus")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.impact.AngledAreaSearchTask")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.impact.AreaOfInterest")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.impact.ImpactLineSearchTask")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.impact.LineOfInterest")));
    EXPECT_EQ(22,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.route.RoutePlanRequest")));
    EXPECT_EQ(23,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.route.RoutePlanResponse")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.task.AssignmentCostMatrix")));
    EXPECT_EQ(2,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.task.SensorFootprintRequests")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.task.TaskAssignmentSummary")));
    EXPECT_EQ(5,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.task.TaskImplementationRequest")));
    EXPECT_EQ(5,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.task.TaskImplementationResponse")));
    EXPECT_EQ(5,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.task.TaskInitialized")));
    EXPECT_EQ(5,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.task.TaskPlanOptions")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.task.UniqueAutomationRequest")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.task.UniqueAutomationResponse")));
    EXPECT_EQ(5,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.uxnative.CreateNewService")));
    //EXPECT_EQ(13,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.uxnative.KillService")));
    
};

TEST(AutomationRequestTest, Test02_Missing_AirVehicleState)
{
    //**************************************************************************
    //  INITIALIZE TEST SETUP
    //**************************************************************************
    // duration_s - number of second to run UxAS
    uint32_t duration_s{3};
    // testPath - relative path to the directory containing configration and othe test files
    std::string testPath("../tests/Test_Utilities/AutomationRequestTests/");
    // uxasConfigurationFile - path and file name of the UxAS configuration file
    std::string uxasConfigurationFile = testPath + "cfg_AutomationRequest_Test02.xml";
    // outputPath - path for saving output files
    std::string outputPath = testPath + "output/";
    // outputPath - path for saving log files
    std::string logPath = outputPath + "log/";
    // initialze the UxAS loggers
    gtestuxascommonLogManagerInitialize(logPath);
    // savedMessagesPath - the path and file name of the saved messages database are returned in this variable
    std::string savedMessagesPath;

    //**************************************************************************
    //  RUN THE TEST
    //**************************************************************************
    bool isReinitialize{true};
    gtestuxastestserviceServiceManagerStartAndRun(duration_s,uxasConfigurationFile, outputPath, savedMessagesPath,isReinitialize);

    //*************************************************************************
    //  CHECK RESULTS
    //*************************************************************************
    // use GoogleTest macros to perform tests on the output
    // CountMessagesInLogDb(savedMessagesPath,messageDescription) - queries the saved messages database 
    // and returns the number of messages with the given "description"
    //   - savedMessagesPath - the path and file name of the saved messages database
    //   - messageDescription - message description of messages to count

    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.uxnative.StartupComplete")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.cmasi.AirVehicleConfiguration")));
    EXPECT_EQ(0,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.cmasi.AirVehicleState")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.cmasi.AreaSearchTask")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.cmasi.AutomationRequest")));
    EXPECT_EQ(0,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.cmasi.AutomationResponse")));
    EXPECT_EQ(2,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.cmasi.KeepOutZone")));
    EXPECT_EQ(2,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.cmasi.LineSearchTask")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.cmasi.OperatingRegion")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.cmasi.ServiceStatus")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.impact.AngledAreaSearchTask")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.impact.AreaOfInterest")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.impact.ImpactLineSearchTask")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.impact.LineOfInterest")));
    EXPECT_EQ(0,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.route.RoutePlanRequest")));
    EXPECT_EQ(0,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.route.RoutePlanResponse")));
    EXPECT_EQ(0,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.task.AssignmentCostMatrix")));
    EXPECT_EQ(0,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.task.SensorFootprintRequests")));
    EXPECT_EQ(0,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.task.TaskAssignmentSummary")));
    EXPECT_EQ(0,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.task.TaskImplementationRequest")));
    EXPECT_EQ(0,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.task.TaskImplementationResponse")));
    EXPECT_EQ(5,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.task.TaskInitialized")));
    EXPECT_EQ(0,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.task.TaskPlanOptions")));
    EXPECT_EQ(0,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.task.UniqueAutomationRequest")));
    EXPECT_EQ(0,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.task.UniqueAutomationResponse")));
    EXPECT_EQ(5,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.uxnative.CreateNewService")));
    //EXPECT_EQ(13,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.uxnative.KillService")));
};

TEST(AutomationRequestTest, Test03_TaskInsideKeepOutVisibility_WrongAnswer)
{
    //**************************************************************************
    //  INITIALIZE TEST SETUP
    //**************************************************************************
    // duration_s - number of second to run UxAS
    uint32_t duration_s{3};
    // testPath - relative path to the directory containing configration and othe test files
    std::string testPath("../tests/Test_Utilities/AutomationRequestTests/");
    // uxasConfigurationFile - path and file name of the UxAS configuration file
    std::string uxasConfigurationFile = testPath + "cfg_AutomationRequest_Test03.xml";
    // outputPath - path for saving output files
    std::string outputPath = testPath + "output/";
    // outputPath - path for saving log files
    std::string logPath = outputPath + "log/";
    // initialze the UxAS loggers
    gtestuxascommonLogManagerInitialize(logPath);
    // savedMessagesPath - the path and file name of the saved messages database are returned in this variable
    std::string savedMessagesPath;

    //**************************************************************************
    //  RUN THE TEST
    //**************************************************************************
    bool isReinitialize{true};
    gtestuxastestserviceServiceManagerStartAndRun(duration_s,uxasConfigurationFile, outputPath, savedMessagesPath,isReinitialize);

    //*************************************************************************
    //  CHECK RESULTS
    //*************************************************************************
    // use GoogleTest macros to perform tests on the output
    // CountMessagesInLogDb(savedMessagesPath,messageDescription) - queries the saved messages database 
    // and returns the number of messages with the given "description"
    //   - savedMessagesPath - the path and file name of the saved messages database
    //   - messageDescription - message description of messages to count

    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.uxnative.StartupComplete")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.cmasi.AirVehicleConfiguration")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.cmasi.AirVehicleState")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.cmasi.AreaSearchTask")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.cmasi.AutomationRequest")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.cmasi.AutomationResponse")));
    EXPECT_EQ(2,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.cmasi.KeepOutZone")));
    EXPECT_EQ(2,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.cmasi.LineSearchTask")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.cmasi.OperatingRegion")));
    EXPECT_EQ(4,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.cmasi.ServiceStatus")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.impact.AngledAreaSearchTask")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.impact.AreaOfInterest")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.impact.ImpactLineSearchTask")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.impact.LineOfInterest")));
    EXPECT_EQ(23,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.route.RoutePlanRequest")));
    EXPECT_EQ(24,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.route.RoutePlanResponse")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.task.AssignmentCostMatrix")));
    EXPECT_EQ(2,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.task.SensorFootprintRequests")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.task.TaskAssignmentSummary")));
    EXPECT_EQ(6,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.task.TaskImplementationRequest")));
    EXPECT_EQ(6,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.task.TaskImplementationResponse")));
    EXPECT_EQ(6,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.task.TaskInitialized")));
    EXPECT_EQ(6,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.task.TaskPlanOptions")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.task.UniqueAutomationRequest")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.task.UniqueAutomationResponse")));
    EXPECT_EQ(6,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.uxnative.CreateNewService")));
    //EXPECT_EQ(14,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.uxnative.KillService")));
    
};

// helper for traversing waypoint list from a mission commmand
afrl::cmasi::Waypoint* wpFromList(int64_t wpID, std::vector<afrl::cmasi::Waypoint*>& wpList)
{
    auto wp = std::find_if(wpList.begin(), wpList.end(), [&](afrl::cmasi::Waypoint* w) { return w ? w->getNumber() == wpID : false; });
    if( wp != wpList.end() )
    {
        return *wp;
    }
    return nullptr;
}

TEST(AutomationRequestTest, Test04_EntityEligibility)
{
    //**************************************************************************
    //  INITIALIZE TEST SETUP
    //**************************************************************************
    // duration_s - number of second to run UxAS
    uint32_t duration_s{3};
    // testPath - relative path to the directory containing configration and othe test files
    std::string testPath("../tests/Test_Utilities/AutomationRequestTests/");
    // uxasConfigurationFile - path and file name of the UxAS configuration file
    std::string uxasConfigurationFile = testPath + "cfg_AutomationRequest_Test04.xml";
    // outputPath - path for saving output files
    std::string outputPath = testPath + "output/";
    // outputPath - path for saving log files
    std::string logPath = outputPath + "log/";
    // initialze the UxAS loggers
    gtestuxascommonLogManagerInitialize(logPath);
    // savedMessagesPath - the path and file name of the saved messages database are returned in this variable
    std::string savedMessagesPath;

    //**************************************************************************
    //  RUN THE TEST
    //**************************************************************************
    bool isReinitialize{true};
    gtestuxastestserviceServiceManagerStartAndRun(duration_s,uxasConfigurationFile, outputPath, savedMessagesPath,isReinitialize);

    //*************************************************************************
    //  CHECK RESULTS
    //*************************************************************************
    // use GoogleTest macros to perform tests on the output
    // CountMessagesInLogDb(savedMessagesPath,messageDescription) - queries the saved messages database 
    // and returns the number of messages with the given "description"
    //   - savedMessagesPath - the path and file name of the saved messages database
    //   - messageDescription - message description of messages to count

    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.uxnative.StartupComplete")));
    EXPECT_EQ(2,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.cmasi.AirVehicleConfiguration")));
    EXPECT_EQ(2,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.cmasi.AirVehicleState")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.cmasi.AutomationRequest")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.cmasi.AutomationResponse")));
    EXPECT_EQ(2,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.cmasi.KeepOutZone")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.cmasi.OperatingRegion")));
    EXPECT_EQ(3,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.cmasi.PointSearchTask")));
    EXPECT_EQ(4,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.cmasi.ServiceStatus")));
    EXPECT_EQ(3,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.route.RoutePlanRequest")));
    EXPECT_EQ(5,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.route.RoutePlanResponse")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.task.AssignmentCostMatrix")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.task.TaskAssignmentSummary")));
    EXPECT_EQ(3,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.task.TaskImplementationRequest")));
    EXPECT_EQ(3,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.task.TaskImplementationResponse")));
    EXPECT_EQ(3,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.task.TaskInitialized")));
    EXPECT_EQ(3,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.task.TaskPlanOptions")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.task.UniqueAutomationRequest")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.task.UniqueAutomationResponse")));
    EXPECT_EQ(3,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.uxnative.CreateNewService")));

    // In addition to counting that the proper number of messages were produced, the specifications should be met.
    // This test requires that:
    //    - 1000 is assigned to complete tasks 12 and 11 (in that order)
    //    - 2000 is assigned to complete task 10 only
    // (This is a combination of both the prescribed Process Algebra relationship as well as "Eligible Entities" for each task)

    std::vector< std::shared_ptr<avtas::lmcp::Object> > msgs;
    ReportMessagesInLogDb(savedMessagesPath, "afrl.cmasi.AutomationResponse", msgs);
    ASSERT_EQ(1, msgs.size());
    ASSERT_TRUE(afrl::cmasi::isAutomationResponse(msgs.at(0)));

    auto response = std::static_pointer_cast<afrl::cmasi::AutomationResponse>(msgs.at(0));
    ASSERT_EQ(2, response->getMissionCommandList().size());
    ASSERT_TRUE( afrl::cmasi::isMissionCommand(response->getMissionCommandList().at(0)) );
    ASSERT_TRUE( afrl::cmasi::isMissionCommand(response->getMissionCommandList().at(1)) );

    auto mish1000 = std::shared_ptr<afrl::cmasi::MissionCommand>(response->getMissionCommandList().at(0)->clone());
    auto mish2000 = std::shared_ptr<afrl::cmasi::MissionCommand>(response->getMissionCommandList().at(1)->clone());
    if(mish1000->getVehicleID() != 1000)
    {
        mish1000.swap(mish2000);
    }
    EXPECT_EQ(1000, mish1000->getVehicleID());
    EXPECT_EQ(2000, mish2000->getVehicleID());

    EXPECT_GT(mish1000->getWaypointList().size(), 0);
    EXPECT_GT(mish2000->getWaypointList().size(), 0);

    // follow waypoints in order for vehicle 1000 starting from 'FirstWaypoint'
    // ensure that 'AssociatedTasks' include Task 12 and 11 in that order
    bool foundTask12 = false;
    bool foundTask11 = false;
    std::vector<int64_t> visitCache;

    auto wp = wpFromList(mish1000->getFirstWaypoint(), mish1000->getWaypointList());
    while(wp && wp->getNextWaypoint() != wp->getNumber() && !foundTask11)
    {
        std::vector<int64_t>::iterator found;

        // re-visiting a waypoint means a circular path, no new waypoints involved
        found = std::find(visitCache.begin(), visitCache.end(), wp->getNumber());
        if(found != visitCache.end())
            break;
        visitCache.push_back(wp->getNumber());
        
        // before looking for task 11, ensure task 12 has been found
        if( foundTask12 )
        {
            found = std::find(wp->getAssociatedTasks().begin(), wp->getAssociatedTasks().end(), 11);
            foundTask11 |= (found != wp->getAssociatedTasks().end());
        }

        // check to see if task 12 is associated with this waypoint
        found = std::find(wp->getAssociatedTasks().begin(), wp->getAssociatedTasks().end(), 12);
        foundTask12 |= (found != wp->getAssociatedTasks().end());

        // go to next waypoint
        wp = wpFromList(wp->getNextWaypoint(), mish1000->getWaypointList());
    }

    EXPECT_TRUE(foundTask12);
    EXPECT_TRUE(foundTask11);

    // follow waypoints in order for vehicle 2000 starting from 'FirstWaypoint'
    // ensure that 'AssociatedTasks' includes Task 10
    bool foundTask10 = false;
    visitCache.clear();

    wp = wpFromList(mish2000->getFirstWaypoint(), mish2000->getWaypointList());
    while(wp && wp->getNextWaypoint() != wp->getNumber() && !foundTask10)
    {
        std::vector<int64_t>::iterator found;

        // re-visiting a waypoint means a circular path, no new waypoints involved
        found = std::find(visitCache.begin(), visitCache.end(), wp->getNumber());
        if(found != visitCache.end())
            break;
        visitCache.push_back(wp->getNumber());
        
        // check to see if task 10 is associated with this waypoint
        found = std::find(wp->getAssociatedTasks().begin(), wp->getAssociatedTasks().end(), 10);
        foundTask10 |= (found != wp->getAssociatedTasks().end());

        // go to next waypoint
        wp = wpFromList(wp->getNextWaypoint(), mish2000->getWaypointList());
    }

    EXPECT_TRUE(foundTask10);

};

int main(int argc, char **argv)
{
    // Build, Google Test run-time and environment tear-down
    ::testing::InitGoogleTest(&argc, argv);
    // Run the tests and return the results
    return RUN_ALL_TESTS();
}

