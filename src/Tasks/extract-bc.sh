#!/bin/bash


function extract_sub {
    BCF=$(basename $1 .cpp).bc
    clang++ -Wno-uninitialized -Wno-return-type -Wno-comment -std=c++11 \
    -I../../zlib-1.2.8 -I../../zlib-1.2.8 -I../../zlib-1.2.8/contrib/minizip -I../../3rd/TinyGPS -I../../3rd/TinyGPS -I../../serial-1.2.1/include -I../../sqlite-amalgamation-3120200 -I../../sqlite-amalgamation-3120200 -I../../SQLiteCpp-1.3.1/include -I../../3rd/PugiXML/src -I../../zeromq-4.1.1/include -I../../czmq-3.0.1/include -I../../cppzmq-4.2.1 -I../../cppzmq-4.2.1 -I../../zyre-1.1.0/include -I../../boost_1_64_0 -I../../boost_1_64_0 -I../../src/Tasks -I../../src/Tasks -I../../src/DPSS -I../../src/DPSS -I../../src/Plans -I../../src/Plans -I../../src/VisilibityLib -I../../src/VisilibityLib -I../../src/Services -I../../src/Services -I../../src/Includes -I../../src/Includes -I../../src/Communications -I../../src/Communications -I../../src/LMCP -I../../src/LMCP -I../../resources/AutomationDiagramDataService -I../../src/Utilities -I../../src/Utilities -fdiagnostics-color=always -pipe -D_FILE_OFFSET_BITS=64 -Wall -Winvalid-pch -Wnon-virtual-dtor -O0 -DLINUX -fPIC -std=c++11 -Wno-unused-function -Wno-unused-variable -emit-llvm -c -o $BCF $1

}

for i in $(ls | grep ".cpp$" ); do
    extract_sub $i
done

