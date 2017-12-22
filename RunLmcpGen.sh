#! /bin/bash -e

HERE=$PWD;

DIRECTORY="../LmcpGen"

if [ -d "${DIRECTORY}" ]; then

	# build lmcpgen
	cd ${DIRECTORY}
	ant -q jar
	cd ${HERE}

	#java -Xmx2048m -jar ../LmcpGen/dist/LmcpGen.jar
	java -Xmx2048m -jar ../LmcpGen/dist/LmcpGen.jar -mdmdir "mdms" -cpp -dir "src/LMCP"
	java -Xmx2048m -jar ../LmcpGen/dist/LmcpGen.jar -mdmdir "mdms" -java -dir "../OpenAMASE/OpenAMASE/lib/LMCP"
	java -Xmx2048m -jar ../LmcpGen/dist/LmcpGen.jar -mdmdir "mdms" -doc -dir "doc/LMCP"
	java -Xmx2048m -jar ../LmcpGen/dist/LmcpGen.jar -mdmdir "mdms" -py -dir "src/LMCP/py"
else
	echo "ERROR: LmcpGen must be present!!!"
	exit 1
fi
