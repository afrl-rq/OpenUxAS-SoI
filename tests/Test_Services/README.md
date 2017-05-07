# Test Organization

The organization and purpose of sub-directories in `OpenUxAS/tests/Test_Services` follows:

 - Each directory is a collection of test sets with each represented by a single `.cpp` file.
 - Each `.cpp` file contains a set of test cases; all test cases are share a single build, run-time and environment tear-down.
 - Each test case defined within a `.cpp` file consists of 1-many tests
 - Each test build is managed by an associated `meson.build` file


# How To Add a Functional Test To Uxas

1. Create a directory for the test:
   - `mkdir uxas/code/tests/Test_Services/SampleTest_Test01`

2. Add a UxAS configuration file and inputs files to the new test directory

3. Make a copy of the functional test template source code:
   - `cp OpenUxAS/tests/Test_Services/GTestFunctionalTestTemplate.cpp OpenUxAS/tests/Test_Services/SampleTest_Test01/SampleTest_Test01.cpp`

4. Edit the new functional test source code to modify, at minimum, the following:
   - `testPath` : Test are run from the `OpenUxas/build` directory, so add the relative path from there to the new test
   - `uxasConfigurationFile` : add the relative path, including file name to UxAS configuration file
   - `(ASSERT_TRUE)` : add/edit the google test statements necessary to test the results

5. Add the new functional test to `meson.build`
   - Add the line `subdir('SampleTest_Test01')` to `OpenUxAS/tests/Test_Services/meson.build`

6. Make a copy of the `meson.build` template for compiling the test
   - `cp OpenUxAS/tests/Test_Services/mesontestbuild.template OpenUxAS/tests/Test_Services/SampleTest_Test01/meson.build`
   - Change all instances of `SampleTest_Test01` to the new test name


