#! /bin/bash -e

HERE=$PWD;

DIRECTORY="../LmcpGen"

if [ -d "${DIRECTORY}" ]; then

	# build lmcpgen
	cd ${DIRECTORY}
	echo " ** building lmcpgen **"
	ant -q jar
	echo " ** finished building lmcpgen **"
	cd ${HERE}

	# auto-create documentation, c++, and python libraries
	echo ""
	echo " ** processing mdms **"
	#java -Xmx2048m -jar ../LmcpGen/dist/LmcpGen.jar
	java -Xmx2048m -jar ../LmcpGen/dist/LmcpGen.jar -mdmdir "mdms" -cpp -dir "src/LMCP"
	java -Xmx2048m -jar ../LmcpGen/dist/LmcpGen.jar -mdmdir "mdms" -java -dir "../OpenAMASE/OpenAMASE/lib/LMCP"
	java -Xmx2048m -jar ../LmcpGen/dist/LmcpGen.jar -mdmdir "mdms" -doc -dir "doc/LMCP"
	java -Xmx2048m -jar ../LmcpGen/dist/LmcpGen.jar -mdmdir "mdms" -py -dir "src/LMCP/py"
	echo " ** finished processing mdms **"

	if [ "$1" = "-a" ]; then
	   # build and install java library for AMASE
	   echo ""
	   echo " ** building java library for AMASE **"
	   java -Xmx2048m -jar ../LmcpGen/dist/LmcpGen.jar -mdmdir "mdms" -java -dir "../OpenAMASE/OpenAMASE/lib/LMCP"
	   cd ../OpenAMASE/OpenAMASE/lib/LMCP
	   ant -q jar
	   cd dist
	   cp lmcplib.jar ../..
	   cd ../../..
	   ant -q jar
	   cd ../../OpenUxAS
	   echo " ** finished building java library for AMASE **"
	fi
	cd ${HERE}


else
	echo "ERROR: LmcpGen must be present!!!"
	exit 1
fi
