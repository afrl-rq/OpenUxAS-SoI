#! /bin/bash

# use LmcpGen via GUI
#java -Xmx2048m -jar ../LmcpGen/dist/LmcpGen.jar

# auto-create documentation, c++, and python libraries
java -Xmx2048m -jar ../LmcpGen/dist/LmcpGen.jar -mdmdir "mdms" -cpp -dir "src/LMCP"
java -Xmx2048m -jar ../LmcpGen/dist/LmcpGen.jar -mdmdir "mdms" -doc -dir "doc/LMCP"
java -Xmx2048m -jar ../LmcpGen/dist/LmcpGen.jar -mdmdir "mdms" -py -dir "src/LMCP/py"

# build and install java library for AMASE
java -Xmx2048m -jar ../LmcpGen/dist/LmcpGen.jar -mdmdir "mdms" -java -dir "../OpenAMASE/OpenAMASE/lib/LMCP"
cd ../OpenAMASE/OpenAMASE/lib/LMCP
ant -q jar
cd dist
cp lmcplib.jar ../..
cd ../../..
ant -q jar
cd ../../OpenUxAS
