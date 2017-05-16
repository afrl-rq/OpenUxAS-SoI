program ras_service, rpvs_service, uxas_env {
    specification test,{1,1,1},Test;
    specification test_reach,{1,1,1},TestReach;

    specification uxas1,{1,1,1},Uxas1;
    specification uxas2,{1,1,1},Uxas2;

    specification uxas_reach1,{1,1,1},UxasReach1;
    specification uxas_reach2,{1,1,1},UxasReach2;
}

procedure ras_service {
    predicate (x == 0);
    abstract {1,LTS};
}

Test = ( configure -> Test1 ).
Test1 = ( process -> Test1 ).

TestReach = ( configure -> process -> ERROR ).

//-- this fails
Uxas1 = ( route_request -> route_response -> Uxas1 ).

//-- this passes
Uxas2 = ( route_request -> Uxas21 ).
Uxas21 = ( route_request -> Uxas21 | route_response -> Uxas21 | route_plan_request -> Uxas21 | route_plan_response -> Uxas21 ).

//-- this fails
UxasReach1 = ( route_request -> route_response -> ERROR ) + {route_request,route_response}.

//-- this passes
UxasReach2 = ( route_request -> route_response -> route_response -> ERROR )
           + {route_request,route_response}.
