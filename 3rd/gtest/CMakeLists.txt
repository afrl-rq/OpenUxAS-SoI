cmake_minimum_required(VERSION 3.3)

##################################################
#
# USAGE:
# cmake CMakeLists.txt
#
##################################################
#
# https://code.google.com/p/googletest/wiki/FAQ#Why_is_it_not_recommended_to_install_a_pre-compiled_copy_of_Goog
# http://www.eriksmistad.no/getting-started-with-google-test-on-ubuntu/
# http://stackoverflow.com/questions/13513905/how-to-properly-setup-googletest-on-linux
# http://crascit.com/2015/07/25/cmake-gtest/
# http://stackoverflow.com/questions/8507723/how-to-start-working-with-gtest-and-cmake
#
##################################################

include("${CMAKE_BINARY_DIR}/uxas_cmake_include")

# download and unpack gtest
configure_file(gtest-CMakeLists.txt "${GTEST_DOWNLOAD_DIR}/CMakeLists.txt" )
execute_process(COMMAND "${CMAKE_COMMAND}" -G "${CMAKE_GENERATOR}" .
  WORKING_DIRECTORY "${CMAKE_BINARY_DIR}/${GTEST_DOWNLOAD_DIR}" )
execute_process(COMMAND "${CMAKE_COMMAND}" --build .
  WORKING_DIRECTORY "${CMAKE_BINARY_DIR}/${GTEST_DOWNLOAD_DIR}" )
execute_process(COMMAND "unzip" "-u" "-qq" "${CMAKE_BINARY_DIR}/${GTEST_DOWNLOAD_DIR}/googletest-prefix/src/${GTEST_VERSIONED_NAME}.zip"
  WORKING_DIRECTORY "${CMAKE_BINARY_DIR}/${GTEST_SRC_DIR}" ) 
