#include "gtest/gtest.h"
#include "GtestuxastestserviceServiceManagerStartAndRun.h"



/*
 * 
 */

// TEST(Parameter01,Parameter02) - Google Test Macro
// Parameter01: "test case" (name of collection of tests)
// Parameter02: "test" (name of test)
TEST(EscortTask_Test01, CorrectNumberMessages)
{
    //**************************************************************************
    //  INITIALIZE TEST SETUP
    //**************************************************************************
	// duration_s - number of second to run UxAS
    uint32_t duration_s{8};
    // The runtime directory for all tests is: "uxas/code/builds/netbeans/nb_8.2/FunctionalTests"
    // testPath - relative path to the directory containing configuration and other test files
    std::string testPath;
    // configFileName - the file name of the UxAS configuration file
    std::string configFileName;
    #ifdef _WIN32
	#include "windows.h"
        SetCurrentDirectory("../../../../../");
    #endif

    testPath = "../tests/Test_Services/00_ExampleTests/99_Test_Tasks/Test_EscortTask/";
    configFileName = "cfg_EscortTask.xml";


    // uxasConfigurationFile - path and file name of the UxAS configuration file
    std::string uxasConfigurationFile = testPath + configFileName;
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

    /**************************************************************************
    *  CHECK RESULTS
    ***************************************************************************
    * use GoogleTest macros to perform tests on the output
    * CountMessagesInLogDb(savedMessagesPath,messageDescription) - queries the saved messages database 
    * 	and returns the number of messages with the given "description"
    * - savedMessagesPath - the path and file name of the saved messages database
    * - messageDescription - message description of messages to count
	*
	*	EXPECT_EQ - Google Test Macro
    */
    EXPECT_EQ( 3, CountMessagesInLogDb(savedMessagesPath, std::string("afrl.cmasi.AirVehicleConfiguration")));
    EXPECT_EQ( 3, CountMessagesInLogDb(savedMessagesPath, std::string("afrl.cmasi.AirVehicleState")));
    EXPECT_EQ( 3, CountMessagesInLogDb(savedMessagesPath, std::string("afrl.cmasi.AutomationRequest")));
    EXPECT_EQ( 3, CountMessagesInLogDb(savedMessagesPath, std::string("afrl.cmasi.AutomationResponse")));
    EXPECT_EQ( 3, CountMessagesInLogDb(savedMessagesPath, std::string("afrl.cmasi.MissionCommand")));
    EXPECT_EQ( 2, CountMessagesInLogDb(savedMessagesPath, std::string("afrl.impact.EscortTask")));
    EXPECT_EQ( 1, CountMessagesInLogDb(savedMessagesPath, std::string("afrl.impact.ImpactLineSearchTask")));
    EXPECT_EQ( 1, CountMessagesInLogDb(savedMessagesPath, std::string("afrl.impact.LineOfInterest")));
    EXPECT_EQ( 3, CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.route.RoutePlanRequest")));
    EXPECT_EQ( 3, CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.task.AssignmentCostMatrix")));
    EXPECT_EQ( 3, CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.task.TaskAssignmentSummary")));
    EXPECT_EQ( 3, CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.task.TaskImplementationRequest")));
    EXPECT_EQ( 3, CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.task.TaskImplementationResponse")));
    EXPECT_EQ( 3, CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.task.TaskInitialized")));
    EXPECT_EQ( 3, CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.task.TaskPlanOptions")));
    EXPECT_EQ( 3, CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.task.UniqueAutomationRequest")));
    EXPECT_EQ( 3, CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.task.UniqueAutomationResponse")));
    EXPECT_EQ( 3, CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.uxnative.CreateNewService")));
    EXPECT_EQ( 1, CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.uxnative.StartupComplete")));
};

int main(int argc, char** argv) {
    // Build, Google Test run-time and environment tear-down
    ::testing::InitGoogleTest(&argc, argv);
    // Run the tests and return the results
    return RUN_ALL_TESTS();
}

