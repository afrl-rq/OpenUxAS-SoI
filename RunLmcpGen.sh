#! /bin/bash

# use LmcpGen via GUI
#java -Xmx2048m -jar ../LmcpGen/dist/LmcpGen.jar

# auto-create documentation, c++, rust, and python libraries
java -Xmx1024m -jar ../LmcpGen/dist/LmcpGen.jar -mdmdir "mdms" -cpp -dir "src/LMCP"
java -Xmx2048m -jar ../LmcpGen/dist/LmcpGen.jar -mdmdir "mdms" -rs -dir "src/LMCP/rs"
java -Xmx1024m -jar ../LmcpGen/dist/LmcpGen.jar -mdmdir "mdms" -doc -dir "doc/LMCP"
java -Xmx1024m -jar ../LmcpGen/dist/LmcpGen.jar -mdmdir "mdms" -py -dir "src/LMCP/py"

if [ "$1" = "-a" ]; then
   # build and install java library for AMASE
   java -Xmx2048m -jar ../LmcpGen/dist/LmcpGen.jar -mdmdir "mdms" -java -dir "../OpenAMASE/OpenAMASE/lib/LMCP"
   cd ../OpenAMASE/OpenAMASE/lib/LMCP
   ant -q jar
   cd dist
   cp lmcplib.jar ../..
   cd ../../..
   ant -q jar
   cd ../../OpenUxAS
fi
