#include "gtest/gtest.h"
#include "GtestuxastestserviceServiceManagerStartAndRun.h"
 
// TEST(Parameter01,Parameter02) - Google Test Macro
// Parameter01: "test case" (name of collection of tests)
// Parameter02: "test" (name of test)
TEST(DistributedCooperation_Test01, CorrectNumberMessages)
{
    //**************************************************************************
    //  INITIALIZE TEST SETUP
    //**************************************************************************
	// duration_s - number of second to run UxAS
    uint32_t duration_s{10};
    // The runtime directory for all tests is: "uxas/code/builds/netbeans/nb_8.2/FunctionalTests"
    // testPath - relative path to the directory containing configration and othe test files
	std::string testPath;
	// configFileName - the file name of the UxAS configuration file
	std::string configFileName;
	#ifdef _WIN32
		#include "windows.h"
		SetCurrentDirectory("../../../../");
	#endif

	testPath = "../tests/Test_Services/00_ExampleTests/03_Test_Example_DistributedCooperation/";
	configFileName = "cfg_DistributedCooperation.xml";


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
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.uxnative.StartupComplete")));
    EXPECT_EQ(3,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.cmasi.AirVehicleConfiguration")));
    EXPECT_EQ(2,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.cmasi.KeepOutZone")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.cmasi.OperatingRegion")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.impact.AreaOfInterest")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.impact.LineOfInterest")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.cmasi.AreaSearchTask")));
    EXPECT_EQ(6,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.uxnative.CreateNewService")));
    EXPECT_EQ(6,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.task.TaskInitialized")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.impact.AngledAreaSearchTask")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.impact.ImpactLineSearchTask")));
    EXPECT_EQ(2,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.cmasi.LineSearchTask")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.task.AssignmentCoordinatorTask")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.cmasi.AirVehicleState")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.task.CoordinatedAutomationRequest")));
    EXPECT_EQ(3,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.task.AssignmentCoordination")));
    //EXPECT_EQ(14,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.uxnative.KillService")));

};

int main(int argc, char **argv)
{
	 // Build, Google Test run-time and environment tear-down
    ::testing::InitGoogleTest(&argc, argv);
    // Run the tests and return the results
    return RUN_ALL_TESTS();
}

