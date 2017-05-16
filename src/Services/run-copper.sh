#!/bin/bash

function to_pp {
    TMPF="$1.tmp.c"
    rm -f $TMPF && touch $TMPF
    echo '#define COPPER 1' >> $TMPF
    echo '#define bool int' >> $TMPF
    echo '#define auto int' >> $TMPF
    echo '#define int64_t int' >> $TMPF
    echo '#define uint32_t int' >> $TMPF
    echo '#define true 1' >> $TMPF
    echo '#define false 0' >> $TMPF
    echo '#define std_chrono_duration int' >> $TMPF
    cat $1 >> $TMPF

    cat $TMPF | sed 's/std::string /int /g' > aa ; mv aa $TMPF
    cat $TMPF | sed 's/std::stringstream /int /g' > aa ; mv aa $TMPF
    cat $TMPF | sed -r 's/<([^>]+)>//g' > aa; mv aa $TMPF
    cat $TMPF | sed -r 's/for /while(0) \/\//g' > aa; mv aa $TMPF
    #cat $TMPF | sed -r 's/for/for(;;) \/\//g' > aa; mv aa $TMPF
    cat $TMPF | sed -r 's/\{true\}/ = true/g' > aa; mv aa $TMPF
    cat $TMPF | sed -r 's/std::shared_ptr /int /g' > aa; mv aa $TMPF
    cat $TMPF | sed -r 's/\(new uxas::messages::route::RoutePlanRequest\)/ = 0/g' > aa; mv aa $TMPF
    cat $TMPF | sed -r 's/\(new uxas::messages::route::RouteResponse\)/ = 0/g' > aa; mv aa $TMPF
    cat $TMPF | sed -r 's/::/_/g' > aa; mv aa $TMPF
    
    gcc -E -o $1.pp $TMPF
}

for i in RouteAggregatorService.c RoutePlannerVisibilityService.c uxas_env.c; do to_pp $i; done

#copper --stat --assign --return --noParAssign --specification test RouteAggregatorService.c.pp RoutePlannerVisibilityService.c.pp uxas_env.c.pp uxas.spec --drawPredAbsLTS --inline --cegar --eager --silentTrans

#copper --stat --assign --return --noParAssign --reach --specification test_reach RouteAggregatorService.c.pp RoutePlannerVisibilityService.c.pp uxas_env.c.pp uxas.spec --drawPredAbsLTS --inline --cegar --eager --silentTrans

copper --stat --assign --return --noParAssign RouteAggregatorService.c.pp RoutePlannerVisibilityService.c.pp uxas_env.c.pp uxas.spec --drawPredAbsLTS --inline --cegar --eager --silentTrans $*
