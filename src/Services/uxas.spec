program ras_service, rpvs_service {
    specification test,{1,1},Test;
    specification test_reach,{1},TestReach;
}

procedure ras_service {
    predicate (x == 0);
    abstract {1,LTS};
}

Test = ( configure -> Test1 ).
Test1 = ( process -> Test1 ).

TestReach = ( alpha -> beta -> return {$0 == 1} -> ERROR ).
