#! /bin/sh

if [ $@ ]; then
    case $1 in
        -h|--h|-help|--help)
            echo "Usage: generate-lmcp-sources.sh [path/to/OpenUxAS/mdms]"
            echo " "
            echo "If no path is given, the script will prompt for a path. The script will then"
            echo "completely remove \`lmcp-src\`, descend into the lmcpgen submodule, do a clean"
            echo "build of lmcpgen, and then use the specified mdms to regenerate \`lmcp-src\`."
            exit 0
            ;;
        *)
            # Boldly assume that the user correctly specified the path to the mdms.
            mdms=$1
        ;;
    esac
else
    echo "Please input the absolute path to the OpenUxAS mdms. For example,"
    echo "\`/Users/Tony/Documents/OpenSource/OpenUxAS/mdms\`"
    echo " "
    printf "> "

    read mdms
fi

printf "Completely removing \`lmcp-src\`..."
rm -rf lmcp-src
echo "done."

printf "Building lmcpgen and generating messages using mdms in \`${mdms}\`..."
cd lmcpgen && \
ant clean 1>/dev/null && \
ant jar 1>/dev/null && \
java -Xmx2048m -jar dist/LmcpGen.jar -mdmdir "${mdms}" -ada -dir ../lmcp-src
echo "done."
