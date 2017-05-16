program ras_service, rpvs_service, uxas_env {
    specification test,{1,1,1},Test;
    specification test_reach,{1,1,1},TestReach;
    specification uxas1,{1,1,1},Uxas1;
    specification uxas_reach1,{1,1,1},UxasReach1;
}

procedure ras_service {
    predicate (x == 0);
    abstract {1,LTS};
}

Test = ( configure -> Test1 ).
Test1 = ( process -> Test1 ).

TestReach = ( configure -> process -> ERROR ).

Uxas1 = ( route_request -> route_plan_request -> route_plan_response -> route_response -> Uxas1 ).
UxasReach1 = ( route_request -> route_response -> ERROR ).
