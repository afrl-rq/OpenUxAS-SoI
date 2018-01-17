Steps to Run OpenUxAS GTests on Windows
===========================================

Installing and Setting Up Google Test Adapter
---------------------------------------------

A work around is required because Visual Studio cannot detect the Unit Tests and the paths set in the tests are not configured properly for the Windows

**To Configure the Google Test Adapter:**

1. Install the Google Test Adapter extension for Visual Studio. This extension is compatible with Visual Studio 2012, 2013, 2015, and 2017. Click  [here](https://marketplace.visualstudio.com/items?itemName=ChristianSoltenborn.GoogleTestAdapter) to reach the download page.

1. Make sure the Google Test Adapter extension is enabled.
  * Open Visual Studio
  * In the Visual Studio menu bar, click the Tools menu item.
  * Now click the Extensions and Updates button. The Extensions and Updates pop up window should appear.
  * In the extensions and updates pop up window, make sure the Google Test Adapter is enabled. This should be located in your installed tools.
  * If the Google Test Adapter was not enabled, close and reopen the OpenUxAS Visual Studio solution.

1. Now open the Test Explorer in Visual Studio. If the test explorer is not visible, click Tests -> Windows -> Test Explorer

You should now be able to run the GTests from the Test Explorer.

Setting Up GTest Paths for Windows Compatibility
------------------------------------------------

Currently the GTest configurations assume that the test executable's path is only 1 level deep from the OpenUxAS directory. When using the Google Test Adapter extension, the executable is in the same directory as the test's respective cpp file.

**To run a GTest:**

1. Make sure to include "windows.h", this includes the SetCurrentDirectory function

1. Open each test's .cpp file. Change the current directory so it points to the OpenUxAS base directory.

An example snippet that can be used in the test's cpp file that maintains compatibility with the Windows, Mac OS, and Linux builds can be seen below:


```cpp

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

```
This snippet is currently used in the DistributedCooperation_test01.CorrectNumberMessages test.
