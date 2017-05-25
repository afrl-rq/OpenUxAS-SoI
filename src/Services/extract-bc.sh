#!/bin/bash

function extract_sub {
    BCF=$(basename $1 .cpp).bc
    clang++ -Wno-uninitialized -Wno-return-type -Wno-comment -std=c++11 -w \
            -I../../3rd/zlib-1.2.8 \
            -I../../3rd/zlib-1.2.8/contrib/minizip \
            -I../../3rd/TinyGPS \
            -I../../3rdserial-1.2.1/include \
            -I../../3rd/sqlite-amalgamation-3120200 \
            -I../../3rd/SQLiteCpp-1.3.1/include \
            -I../../3rd/PugiXML/src \
            -I../../3rd/zeromq-4.1.1/include \
            -I../../3rd/czmq-3.0.1/include \
            -I../../3rd/cppzmq-4.2.1 \
            -I../../3rd/zyre-1.1.0/include \
            -I../../src/Tasks \
            -I../../src/DPSS \
            -I../../src/Plans \
            -I../../src/VisilibityLib \
            -I../../src/Services \
            -I../../src/Includes \
            -I../../src/Communications \
            -I../../src/LMCP \
            -I../../src/Utilities \
            -I../../build/src/Includes \
            -I../../resources/AutomationDiagramDataService \
            -fdiagnostics-color=always -pipe -D_FILE_OFFSET_BITS=64 -Wall -Winvalid-pch \
            -Wnon-virtual-dtor -O0 -DLINUX -fPIC -std=c++11 -Wno-unused-function \
            -Wno-unused-variable -emit-llvm -c -o $BCF $1
}

for i in $(ls | grep ".cpp$" ); do
    extract_sub $i
done
