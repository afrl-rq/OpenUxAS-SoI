#!/bin/bash


function extract_sub {
    BCF=$(basename $1 .cpp).bc
    clang++ -Wno-uninitialized -Wno-return-type -Wno-comment -Wno-empty-body -std=c++11 \
            -I../../czmq-3.0.1/include -I../../src/Tasks \
            -I../../build/src/Includes -I../../SQLiteCpp-1.3.1/include \
            -I../../resources/AutomationDiagramDataService \
            -I../../src/Plans -I../../src/DPSS -I../../src/VisilibityLib \
            -I../../zeromq-4.1.1/include -I../../cppzmq-4.2.1 -I../../src/LMCP \
            -I../../src/Includes -I../../src/Communications -I../../src/Utilities \
            -I../../3rd/PugiXML/src -emit-llvm -c \
            -o $BCF $1
    echo "=========== SUB $1 ==============="
    llvm-dis < $BCF | grep addSubscriptionAddress | awk -F'@' '{print $3}' | \
        sed 's/B5cxx11E)//g' | sed 's/^_ZN4//g' | sed 's/12Subscription$/::Subscription/g' | \
        sed -r 's/afrl[0-9]+/afrl::/g' | sed -r 's/uxas8/uxas::/g' | \
        sed -r 's/cmasi[0-9]+/cmasi::/g' | sed -r 's/impact[0-9]+/impact::/g' | \
        sed -r 's/messages[0-9]+/messages::/g' | sed -r 's/route[0-9]+/route::/g' | \
        sed -r 's/task[0-9]+/task::/g'
}

for i in RouteAggregatorService.cpp RoutePlannerVisibilityService.cpp; do
    extract_sub $i
done

