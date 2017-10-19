; Generated using "SADL Requirements Language to ACL2 Sedan" Translator Version 1.98
(in-package "ACL2S")
(set-ignore-ok t)
(defttag :progn!)
(include-book "requirements-analyses-book")

(defdata |translator_generated_name^http://sadl.org/RequestAggregator.sadl#mID^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo^http://sadl.org/RequestAggregator.sadl#rrm^http://sadl.org/RequestAggregator.sadl#RouteRequestMsg^http://sadl.org/RequestAggregator.sadl#receive1^http://sadl.org/RequestAggregator.sadl#ReqAggregator| (enum '(|http://www.w3.org/2001/XMLSchema#string| )))
(deffconst |*translator_generated_name^http://sadl.org/RequestAggregator.sadl#mID^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo^http://sadl.org/RequestAggregator.sadl#rrm^http://sadl.org/RequestAggregator.sadl#RouteRequestMsg^http://sadl.org/RequestAggregator.sadl#receive1^http://sadl.org/RequestAggregator.sadl#ReqAggregator-VALS*| (quote-all |*translator_generated_name^http://sadl.org/RequestAggregator.sadl#mID^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo^http://sadl.org/RequestAggregator.sadl#rrm^http://sadl.org/RequestAggregator.sadl#RouteRequestMsg^http://sadl.org/RequestAggregator.sadl#receive1^http://sadl.org/RequestAggregator.sadl#ReqAggregator-VALUES*|))
(displayname |http://sadl.org/RequestAggregator.sadl#mID^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo^http://sadl.org/RequestAggregator.sadl#rrm^http://sadl.org/RequestAggregator.sadl#RouteRequestMsg^http://sadl.org/RequestAggregator.sadl#receive1^http://sadl.org/RequestAggregator.sadl#ReqAggregator| |mID of RouteRequestInfo of rrm of RouteRequestMsg of receive1 of ReqAggregator|)
(displayname |http://sadl.org/RequestAggregator.sadl#mID^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo^http://sadl.org/RequestAggregator.sadl#rrm^http://sadl.org/RequestAggregator.sadl#RouteRequestMsg^http://sadl.org/RequestAggregator.sadl#receive1^http://sadl.org/RequestAggregator.sadl#ReqAggregatorP| |mID of RouteRequestInfo of rrm of RouteRequestMsg of receive1 of ReqAggregatorP|)
(displayname |translator_generated_name^http://sadl.org/RequestAggregator.sadl#mID^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo^http://sadl.org/RequestAggregator.sadl#rrm^http://sadl.org/RequestAggregator.sadl#RouteRequestMsg^http://sadl.org/RequestAggregator.sadl#receive1^http://sadl.org/RequestAggregator.sadl#ReqAggregator| |translator generated name for mID of RouteRequestInfo of rrm of RouteRequestMsg of receive1 of ReqAggregator|)
(displayname |translator_generated_name^http://sadl.org/RequestAggregator.sadl#mID^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo^http://sadl.org/RequestAggregator.sadl#rrm^http://sadl.org/RequestAggregator.sadl#RouteRequestMsg^http://sadl.org/RequestAggregator.sadl#receive1^http://sadl.org/RequestAggregator.sadl#ReqAggregatorP| |translator generated name for mID of RouteRequestInfo of rrm of RouteRequestMsg of receive1 of ReqAggregatorP|)
(displayname |*http://sadl.org/RequestAggregator.sadl#mID^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo^http://sadl.org/RequestAggregator.sadl#rrm^http://sadl.org/RequestAggregator.sadl#RouteRequestMsg^http://sadl.org/RequestAggregator.sadl#receive1^http://sadl.org/RequestAggregator.sadl#ReqAggregator-VALS*| |*mID of RouteRequestInfo of rrm of RouteRequestMsg of receive1 of ReqAggregator-VALS*|)
(displayname |*http://sadl.org/RequestAggregator.sadl#mID^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo^http://sadl.org/RequestAggregator.sadl#rrm^http://sadl.org/RequestAggregator.sadl#RouteRequestMsg^http://sadl.org/RequestAggregator.sadl#receive1^http://sadl.org/RequestAggregator.sadl#ReqAggregator-VALUES*| |*mID of RouteRequestInfo of rrm of RouteRequestMsg of receive1 of ReqAggregator-VALUES*|)
(displayname |*translator_generated_name^http://sadl.org/RequestAggregator.sadl#mID^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo^http://sadl.org/RequestAggregator.sadl#rrm^http://sadl.org/RequestAggregator.sadl#RouteRequestMsg^http://sadl.org/RequestAggregator.sadl#receive1^http://sadl.org/RequestAggregator.sadl#ReqAggregator-VALS*| |*translator generated name for mID of RouteRequestInfo of rrm of RouteRequestMsg of receive1 of ReqAggregator-VALS*|)
(displayname |*translator_generated_name^http://sadl.org/RequestAggregator.sadl#mID^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo^http://sadl.org/RequestAggregator.sadl#rrm^http://sadl.org/RequestAggregator.sadl#RouteRequestMsg^http://sadl.org/RequestAggregator.sadl#receive1^http://sadl.org/RequestAggregator.sadl#ReqAggregator-VALUES*| |*translator generated name for mID of RouteRequestInfo of rrm of RouteRequestMsg of receive1 of ReqAggregator-VALUES*|)

(defdata |translator_generated_name^rareq_xindex| POS)
;(datavariable |rareq_xindex|)

(displayname |rareq_xindex| |rareq_xindex|)
(displayname |rareq_xindexP| |rareq_xindexP|)
(displayname |translator_generated_name^rareq_xindex| |translator generated name for rareq_xindex|)
(displayname |translator_generated_name^rareq_xindexP| |translator generated name for rareq_xindexP|)
(displayname |*rareq_xindex-VALS*| |*rareq_xindex-VALS*|)
(displayname |*rareq_xindex-VALUES*| |*rareq_xindex-VALUES*|)
(displayname |*translator_generated_name^rareq_xindex-VALS*| |*translator generated name for rareq_xindex-VALS*|)
(displayname |*translator_generated_name^rareq_xindex-VALUES*| |*translator generated name for rareq_xindex-VALUES*|)

(defdata |translator_generated_name^translator_intermediate_variable_4^http://sadl.org/RequestAggregator.sadl#vi^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo^http://sadl.org/RequestAggregator.sadl#rrm^http://sadl.org/RequestAggregator.sadl#RouteRequestMsg^http://sadl.org/RequestAggregator.sadl#receive1^http://sadl.org/RequestAggregator.sadl#ReqAggregator| (enum '(|http://sadl.org/RequestAggregator.sadl#VehiclePlanInfo| )))
(defdata |translator_generated_name^http://sadl.org/RequestAggregator.sadl#vi^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo^http://sadl.org/RequestAggregator.sadl#rrm^http://sadl.org/RequestAggregator.sadl#RouteRequestMsg^http://sadl.org/RequestAggregator.sadl#receive1^http://sadl.org/RequestAggregator.sadl#ReqAggregator| (listof |translator_generated_name^translator_intermediate_variable_4^http://sadl.org/RequestAggregator.sadl#vi^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo^http://sadl.org/RequestAggregator.sadl#rrm^http://sadl.org/RequestAggregator.sadl#RouteRequestMsg^http://sadl.org/RequestAggregator.sadl#receive1^http://sadl.org/RequestAggregator.sadl#ReqAggregator|))
(displayname |translator_intermediate_variable_4^http://sadl.org/RequestAggregator.sadl#vi^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo^http://sadl.org/RequestAggregator.sadl#rrm^http://sadl.org/RequestAggregator.sadl#RouteRequestMsg^http://sadl.org/RequestAggregator.sadl#receive1^http://sadl.org/RequestAggregator.sadl#ReqAggregator| |translator_intermediate_variable_4 of vi of RouteRequestInfo of rrm of RouteRequestMsg of receive1 of ReqAggregator|)
(displayname |translator_intermediate_variable_4^http://sadl.org/RequestAggregator.sadl#vi^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo^http://sadl.org/RequestAggregator.sadl#rrm^http://sadl.org/RequestAggregator.sadl#RouteRequestMsg^http://sadl.org/RequestAggregator.sadl#receive1^http://sadl.org/RequestAggregator.sadl#ReqAggregatorP| |translator_intermediate_variable_4 of vi of RouteRequestInfo of rrm of RouteRequestMsg of receive1 of ReqAggregatorP|)
(displayname |translator_generated_name^translator_intermediate_variable_4^http://sadl.org/RequestAggregator.sadl#vi^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo^http://sadl.org/RequestAggregator.sadl#rrm^http://sadl.org/RequestAggregator.sadl#RouteRequestMsg^http://sadl.org/RequestAggregator.sadl#receive1^http://sadl.org/RequestAggregator.sadl#ReqAggregator| |translator generated name for translator_intermediate_variable_4 of vi of RouteRequestInfo of rrm of RouteRequestMsg of receive1 of ReqAggregator|)
(displayname |translator_generated_name^translator_intermediate_variable_4^http://sadl.org/RequestAggregator.sadl#vi^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo^http://sadl.org/RequestAggregator.sadl#rrm^http://sadl.org/RequestAggregator.sadl#RouteRequestMsg^http://sadl.org/RequestAggregator.sadl#receive1^http://sadl.org/RequestAggregator.sadl#ReqAggregatorP| |translator generated name for translator_intermediate_variable_4 of vi of RouteRequestInfo of rrm of RouteRequestMsg of receive1 of ReqAggregatorP|)
(displayname |http://sadl.org/RequestAggregator.sadl#vi^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo^http://sadl.org/RequestAggregator.sadl#rrm^http://sadl.org/RequestAggregator.sadl#RouteRequestMsg^http://sadl.org/RequestAggregator.sadl#receive1^http://sadl.org/RequestAggregator.sadl#ReqAggregator| |vi of RouteRequestInfo of rrm of RouteRequestMsg of receive1 of ReqAggregator|)
(displayname |http://sadl.org/RequestAggregator.sadl#vi^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo^http://sadl.org/RequestAggregator.sadl#rrm^http://sadl.org/RequestAggregator.sadl#RouteRequestMsg^http://sadl.org/RequestAggregator.sadl#receive1^http://sadl.org/RequestAggregator.sadl#ReqAggregatorP| |vi of RouteRequestInfo of rrm of RouteRequestMsg of receive1 of ReqAggregatorP|)
(displayname |translator_generated_name^http://sadl.org/RequestAggregator.sadl#vi^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo^http://sadl.org/RequestAggregator.sadl#rrm^http://sadl.org/RequestAggregator.sadl#RouteRequestMsg^http://sadl.org/RequestAggregator.sadl#receive1^http://sadl.org/RequestAggregator.sadl#ReqAggregator| |translator generated name for vi of RouteRequestInfo of rrm of RouteRequestMsg of receive1 of ReqAggregator|)
(displayname |translator_generated_name^http://sadl.org/RequestAggregator.sadl#vi^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo^http://sadl.org/RequestAggregator.sadl#rrm^http://sadl.org/RequestAggregator.sadl#RouteRequestMsg^http://sadl.org/RequestAggregator.sadl#receive1^http://sadl.org/RequestAggregator.sadl#ReqAggregatorP| |translator generated name for vi of RouteRequestInfo of rrm of RouteRequestMsg of receive1 of ReqAggregatorP|)

(defdata |translator_generated_name^http://sadl.org/RequestAggregator.sadl#send1^http://sadl.org/RequestAggregator.sadl#ReqAggregator| (enum '(|http://sadl.org/RequestAggregator.sadl#RoutePlanRequestMsg| )))
(deffconst |*translator_generated_name^http://sadl.org/RequestAggregator.sadl#send1^http://sadl.org/RequestAggregator.sadl#ReqAggregator-VALS*| (quote-all |*translator_generated_name^http://sadl.org/RequestAggregator.sadl#send1^http://sadl.org/RequestAggregator.sadl#ReqAggregator-VALUES*|))
(displayname |http://sadl.org/RequestAggregator.sadl#send1^http://sadl.org/RequestAggregator.sadl#ReqAggregator| |send1 of ReqAggregator|)
(displayname |http://sadl.org/RequestAggregator.sadl#send1^http://sadl.org/RequestAggregator.sadl#ReqAggregatorP| |send1 of ReqAggregatorP|)
(displayname |translator_generated_name^http://sadl.org/RequestAggregator.sadl#send1^http://sadl.org/RequestAggregator.sadl#ReqAggregator| |translator generated name for send1 of ReqAggregator|)
(displayname |translator_generated_name^http://sadl.org/RequestAggregator.sadl#send1^http://sadl.org/RequestAggregator.sadl#ReqAggregatorP| |translator generated name for send1 of ReqAggregatorP|)
(displayname |*http://sadl.org/RequestAggregator.sadl#send1^http://sadl.org/RequestAggregator.sadl#ReqAggregator-VALS*| |*send1 of ReqAggregator-VALS*|)
(displayname |*http://sadl.org/RequestAggregator.sadl#send1^http://sadl.org/RequestAggregator.sadl#ReqAggregator-VALUES*| |*send1 of ReqAggregator-VALUES*|)
(displayname |*translator_generated_name^http://sadl.org/RequestAggregator.sadl#send1^http://sadl.org/RequestAggregator.sadl#ReqAggregator-VALS*| |*translator generated name for send1 of ReqAggregator-VALS*|)
(displayname |*translator_generated_name^http://sadl.org/RequestAggregator.sadl#send1^http://sadl.org/RequestAggregator.sadl#ReqAggregator-VALUES*| |*translator generated name for send1 of ReqAggregator-VALUES*|)

(defdata |translator_generated_name^http://sadl.org/RequestAggregator.sadl#mID^http://sadl.org/RequestAggregator.sadl#RoutePlanRequestMsg| (enum '(|http://www.w3.org/2001/XMLSchema#string| )))
(deffconst |*translator_generated_name^http://sadl.org/RequestAggregator.sadl#mID^http://sadl.org/RequestAggregator.sadl#RoutePlanRequestMsg-VALS*| (quote-all |*translator_generated_name^http://sadl.org/RequestAggregator.sadl#mID^http://sadl.org/RequestAggregator.sadl#RoutePlanRequestMsg-VALUES*|))
(displayname |http://sadl.org/RequestAggregator.sadl#mID^http://sadl.org/RequestAggregator.sadl#RoutePlanRequestMsg| |mID of RoutePlanRequestMsg|)
(displayname |http://sadl.org/RequestAggregator.sadl#mID^http://sadl.org/RequestAggregator.sadl#RoutePlanRequestMsgP| |mID of RoutePlanRequestMsgP|)
(displayname |translator_generated_name^http://sadl.org/RequestAggregator.sadl#mID^http://sadl.org/RequestAggregator.sadl#RoutePlanRequestMsg| |translator generated name for mID of RoutePlanRequestMsg|)
(displayname |translator_generated_name^http://sadl.org/RequestAggregator.sadl#mID^http://sadl.org/RequestAggregator.sadl#RoutePlanRequestMsgP| |translator generated name for mID of RoutePlanRequestMsgP|)
(displayname |*http://sadl.org/RequestAggregator.sadl#mID^http://sadl.org/RequestAggregator.sadl#RoutePlanRequestMsg-VALS*| |*mID of RoutePlanRequestMsg-VALS*|)
(displayname |*http://sadl.org/RequestAggregator.sadl#mID^http://sadl.org/RequestAggregator.sadl#RoutePlanRequestMsg-VALUES*| |*mID of RoutePlanRequestMsg-VALUES*|)
(displayname |*translator_generated_name^http://sadl.org/RequestAggregator.sadl#mID^http://sadl.org/RequestAggregator.sadl#RoutePlanRequestMsg-VALS*| |*translator generated name for mID of RoutePlanRequestMsg-VALS*|)
(displayname |*translator_generated_name^http://sadl.org/RequestAggregator.sadl#mID^http://sadl.org/RequestAggregator.sadl#RoutePlanRequestMsg-VALUES*| |*translator generated name for mID of RoutePlanRequestMsg-VALUES*|)

(defdata |translator_generated_name^http://sadl.org/RequestAggregator.sadl#vehicleInfo^http://sadl.org/RequestAggregator.sadl#RoutePlanRequestMsg| (enum '(|http://sadl.org/RequestAggregator.sadl#VehiclePlanInfo| )))
(deffconst |*translator_generated_name^http://sadl.org/RequestAggregator.sadl#vehicleInfo^http://sadl.org/RequestAggregator.sadl#RoutePlanRequestMsg-VALS*| (quote-all |*translator_generated_name^http://sadl.org/RequestAggregator.sadl#vehicleInfo^http://sadl.org/RequestAggregator.sadl#RoutePlanRequestMsg-VALUES*|))
(displayname |http://sadl.org/RequestAggregator.sadl#vehicleInfo^http://sadl.org/RequestAggregator.sadl#RoutePlanRequestMsg| |vehicleInfo of RoutePlanRequestMsg|)
(displayname |http://sadl.org/RequestAggregator.sadl#vehicleInfo^http://sadl.org/RequestAggregator.sadl#RoutePlanRequestMsgP| |vehicleInfo of RoutePlanRequestMsgP|)
(displayname |translator_generated_name^http://sadl.org/RequestAggregator.sadl#vehicleInfo^http://sadl.org/RequestAggregator.sadl#RoutePlanRequestMsg| |translator generated name for vehicleInfo of RoutePlanRequestMsg|)
(displayname |translator_generated_name^http://sadl.org/RequestAggregator.sadl#vehicleInfo^http://sadl.org/RequestAggregator.sadl#RoutePlanRequestMsgP| |translator generated name for vehicleInfo of RoutePlanRequestMsgP|)
(displayname |*http://sadl.org/RequestAggregator.sadl#vehicleInfo^http://sadl.org/RequestAggregator.sadl#RoutePlanRequestMsg-VALS*| |*vehicleInfo of RoutePlanRequestMsg-VALS*|)
(displayname |*http://sadl.org/RequestAggregator.sadl#vehicleInfo^http://sadl.org/RequestAggregator.sadl#RoutePlanRequestMsg-VALUES*| |*vehicleInfo of RoutePlanRequestMsg-VALUES*|)
(displayname |*translator_generated_name^http://sadl.org/RequestAggregator.sadl#vehicleInfo^http://sadl.org/RequestAggregator.sadl#RoutePlanRequestMsg-VALS*| |*translator generated name for vehicleInfo of RoutePlanRequestMsg-VALS*|)
(displayname |*translator_generated_name^http://sadl.org/RequestAggregator.sadl#vehicleInfo^http://sadl.org/RequestAggregator.sadl#RoutePlanRequestMsg-VALUES*| |*translator generated name for vehicleInfo of RoutePlanRequestMsg-VALUES*|)

(defdata |translator_generated_name^http://sadl.org/RequestAggregator.sadl#RoutePlanRequestMsg| (enum '(|http://sadl.org/RequestAggregator.sadl#RoutePlanRequestMsg|)))
(deffconst |*translator_generated_name^http://sadl.org/RequestAggregator.sadl#RoutePlanRequestMsg-VALS*| (quote-all |*translator_generated_name^http://sadl.org/RequestAggregator.sadl#RoutePlanRequestMsg-VALUES*|))
(defdecomposition |rareq_vpr|
((|inputvar1| |translator_generated_name^http://sadl.org/RequestAggregator.sadl#mID^http://sadl.org/RequestAggregator.sadl#RoutePlanRequestMsgP|)
(|inputvar2| |translator_generated_name^http://sadl.org/RequestAggregator.sadl#vehicleInfo^http://sadl.org/RequestAggregator.sadl#RoutePlanRequestMsgP|))
((|outputvar| |translator_generated_name^http://sadl.org/RequestAggregator.sadl#RoutePlanRequestMsgP|)))

(defrequirement R2_instance_1
  (    (|http://sadl.org/RequestAggregator.sadl#mID^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo^http://sadl.org/RequestAggregator.sadl#rrm^http://sadl.org/RequestAggregator.sadl#RouteRequestMsg^http://sadl.org/RequestAggregator.sadl#receive1^http://sadl.org/RequestAggregator.sadl#ReqAggregator| |translator_generated_name^http://sadl.org/RequestAggregator.sadl#mID^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo^http://sadl.org/RequestAggregator.sadl#rrm^http://sadl.org/RequestAggregator.sadl#RouteRequestMsg^http://sadl.org/RequestAggregator.sadl#receive1^http://sadl.org/RequestAggregator.sadl#ReqAggregatorP|)
    (|rareq_xindex| |translator_generated_name^rareq_xindexP|)
    (|http://sadl.org/RequestAggregator.sadl#vi^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo^http://sadl.org/RequestAggregator.sadl#rrm^http://sadl.org/RequestAggregator.sadl#RouteRequestMsg^http://sadl.org/RequestAggregator.sadl#receive1^http://sadl.org/RequestAggregator.sadl#ReqAggregator| |translator_generated_name^http://sadl.org/RequestAggregator.sadl#vi^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo^http://sadl.org/RequestAggregator.sadl#rrm^http://sadl.org/RequestAggregator.sadl#RouteRequestMsg^http://sadl.org/RequestAggregator.sadl#receive1^http://sadl.org/RequestAggregator.sadl#ReqAggregatorP|)
  )
  (    (|http://sadl.org/RequestAggregator.sadl#send1^http://sadl.org/RequestAggregator.sadl#ReqAggregator| |translator_generated_name^http://sadl.org/RequestAggregator.sadl#send1^http://sadl.org/RequestAggregator.sadl#ReqAggregatorP|)
  )
(rimplies T (equal |http://sadl.org/RequestAggregator.sadl#send1^http://sadl.org/RequestAggregator.sadl#ReqAggregator| (|rareq_vpr| |http://sadl.org/RequestAggregator.sadl#mID^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo^http://sadl.org/RequestAggregator.sadl#rrm^http://sadl.org/RequestAggregator.sadl#RouteRequestMsg^http://sadl.org/RequestAggregator.sadl#receive1^http://sadl.org/RequestAggregator.sadl#ReqAggregator| (nth-element |rareq_xindex| |http://sadl.org/RequestAggregator.sadl#vi^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo^http://sadl.org/RequestAggregator.sadl#rrm^http://sadl.org/RequestAggregator.sadl#RouteRequestMsg^http://sadl.org/RequestAggregator.sadl#receive1^http://sadl.org/RequestAggregator.sadl#ReqAggregator|)))))

(SRL-meta-data 
  requirement-history 
  ((:SRL-name R2)
   (:Context 1)
   (:transformations ((grounding R2_instance_1)))
   (:RA-name R2_instance_1)
   (:ModelGenFile "")
   (:VarMapFile "")
      (:Variables ((
                  (:name |http://sadl.org/RequestAggregator.sadl#mID^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo^http://sadl.org/RequestAggregator.sadl#rrm^http://sadl.org/RequestAggregator.sadl#RouteRequestMsg^http://sadl.org/RequestAggregator.sadl#receive1^http://sadl.org/RequestAggregator.sadl#ReqAggregator|)
                  (:display-name |mID of RouteRequestInfo of rrm of RouteRequestMsg of receive1 of ReqAggregator|)
                  (:SRL-names (|mID of rrm of RouteRequestMsg|))
                  (:direction monitored)
                  (:type string)
                  (:functional-max :unspecified)
                  (:functional-min :unspecified)
                  (:tolerance :unspecified)
                  (:resolution :unspecified)
                  (:event-variable? nil)
                  (:no-contingency-checking? nil)
                  )
                  (
                  (:name |http://sadl.org/RequestAggregator.sadl#vi^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo^http://sadl.org/RequestAggregator.sadl#rrm^http://sadl.org/RequestAggregator.sadl#RouteRequestMsg^http://sadl.org/RequestAggregator.sadl#receive1^http://sadl.org/RequestAggregator.sadl#ReqAggregator|)
                  (:display-name |vi of RouteRequestInfo of rrm of RouteRequestMsg of receive1 of ReqAggregator|)
                  (:SRL-names (|vi of rrm of RouteRequestMsg|))
                  (:direction monitored)
                  (:type list)
                  (:min-length 1)
                  (:max-length 10)
                  (:event-variable? nil)
                  (:no-contingency-checking? nil)
                  )
                  (
                  (:name |http://sadl.org/RequestAggregator.sadl#send1^http://sadl.org/RequestAggregator.sadl#ReqAggregator|)
                  (:display-name |send1 of ReqAggregator|)
                  (:SRL-names (|send1 of ReqAggregator|))
                  (:direction controlled)
                  (:type enum)
                  (:event-variable? t)
                  (:no-contingency-checking? nil)
                  )))
  )
)

(SRL-meta-data 
  context 
  ((:context-id 1)
   (:exp (|ReqAggregator with receive1 RouteRequestMsg|))))


(defassumption A1_instance_2
    (    (|http://sadl.org/RequestAggregator.sadl#vi^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo^http://sadl.org/RequestAggregator.sadl#rrm^http://sadl.org/RequestAggregator.sadl#RouteRequestMsg^http://sadl.org/RequestAggregator.sadl#receive1^http://sadl.org/RequestAggregator.sadl#ReqAggregator| |translator_generated_name^http://sadl.org/RequestAggregator.sadl#vi^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo^http://sadl.org/RequestAggregator.sadl#rrm^http://sadl.org/RequestAggregator.sadl#RouteRequestMsg^http://sadl.org/RequestAggregator.sadl#receive1^http://sadl.org/RequestAggregator.sadl#ReqAggregatorP|)
    (|rareq_xindex| |translator_generated_name^rareq_xindexP|)
  )
  (<= |rareq_xindex| (len-c |http://sadl.org/RequestAggregator.sadl#vi^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo^http://sadl.org/RequestAggregator.sadl#rrm^http://sadl.org/RequestAggregator.sadl#RouteRequestMsg^http://sadl.org/RequestAggregator.sadl#receive1^http://sadl.org/RequestAggregator.sadl#ReqAggregator|)))

(SRL-meta-data 
  assumption-history 
  ((:SRL-name A1)
   (:Context 1)
   (:transformations ((dnf-transformation head A1_instance_0) (dnf-transformation body A1_instance_1) (grounding A1_instance_2)))
   (:Assumption-name A1_instance_2)
   (:ModelGenFile "")
   (:VarMapFile "")
      (:Variables ((
                  (:name |http://sadl.org/RequestAggregator.sadl#vi^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo^http://sadl.org/RequestAggregator.sadl#rrm^http://sadl.org/RequestAggregator.sadl#RouteRequestMsg^http://sadl.org/RequestAggregator.sadl#receive1^http://sadl.org/RequestAggregator.sadl#ReqAggregator|)
                  (:display-name |vi of RouteRequestInfo of rrm of RouteRequestMsg of receive1 of ReqAggregator|)
                  (:SRL-names (|vi of rrm of RouteRequestMsg|))
                  (:direction monitored)
                  (:type list)
                  (:min-length 1)
                  (:max-length 10)
                  (:event-variable? nil)
                  )
                  ))
  )
)


(defassumption A2_instance_5
    (    (|http://sadl.org/RequestAggregator.sadl#vi^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo^http://sadl.org/RequestAggregator.sadl#rrm^http://sadl.org/RequestAggregator.sadl#RouteRequestMsg^http://sadl.org/RequestAggregator.sadl#receive1^http://sadl.org/RequestAggregator.sadl#ReqAggregator| |translator_generated_name^http://sadl.org/RequestAggregator.sadl#vi^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo^http://sadl.org/RequestAggregator.sadl#rrm^http://sadl.org/RequestAggregator.sadl#RouteRequestMsg^http://sadl.org/RequestAggregator.sadl#receive1^http://sadl.org/RequestAggregator.sadl#ReqAggregatorP|)
  )
  (> (len-c |http://sadl.org/RequestAggregator.sadl#vi^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo^http://sadl.org/RequestAggregator.sadl#rrm^http://sadl.org/RequestAggregator.sadl#RouteRequestMsg^http://sadl.org/RequestAggregator.sadl#receive1^http://sadl.org/RequestAggregator.sadl#ReqAggregator|) 0))

(SRL-meta-data 
  assumption-history 
  ((:SRL-name A2)
   (:Context 1)
   (:transformations ((dnf-transformation head A2_instance_3) (dnf-transformation body A2_instance_4) (grounding A2_instance_5)))
   (:Assumption-name A2_instance_5)
   (:ModelGenFile "")
   (:VarMapFile "")
      (:Variables ((
                  (:name |http://sadl.org/RequestAggregator.sadl#vi^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo^http://sadl.org/RequestAggregator.sadl#rrm^http://sadl.org/RequestAggregator.sadl#RouteRequestMsg^http://sadl.org/RequestAggregator.sadl#receive1^http://sadl.org/RequestAggregator.sadl#ReqAggregator|)
                  (:display-name |vi of RouteRequestInfo of rrm of RouteRequestMsg of receive1 of ReqAggregator|)
                  (:SRL-names (|vi of rrm of RouteRequestMsg|))
                  (:direction monitored)
                  (:type list)
                  (:min-length 1)
                  (:max-length 10)
                  (:event-variable? nil)
                  )
                  ))
  )
)


(defassumption A3_instance_8
    (    (|http://sadl.org/RequestAggregator.sadl#vi^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo^http://sadl.org/RequestAggregator.sadl#rrm^http://sadl.org/RequestAggregator.sadl#RouteRequestMsg^http://sadl.org/RequestAggregator.sadl#receive1^http://sadl.org/RequestAggregator.sadl#ReqAggregator| |translator_generated_name^http://sadl.org/RequestAggregator.sadl#vi^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo^http://sadl.org/RequestAggregator.sadl#rrm^http://sadl.org/RequestAggregator.sadl#RouteRequestMsg^http://sadl.org/RequestAggregator.sadl#receive1^http://sadl.org/RequestAggregator.sadl#ReqAggregatorP|)
  )
  (<= (len-c |http://sadl.org/RequestAggregator.sadl#vi^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo^http://sadl.org/RequestAggregator.sadl#rrm^http://sadl.org/RequestAggregator.sadl#RouteRequestMsg^http://sadl.org/RequestAggregator.sadl#receive1^http://sadl.org/RequestAggregator.sadl#ReqAggregator|) 10))

(SRL-meta-data 
  assumption-history 
  ((:SRL-name A3)
   (:Context 1)
   (:transformations ((dnf-transformation head A3_instance_6) (dnf-transformation body A3_instance_7) (grounding A3_instance_8)))
   (:Assumption-name A3_instance_8)
   (:ModelGenFile "")
   (:VarMapFile "")
      (:Variables ((
                  (:name |http://sadl.org/RequestAggregator.sadl#vi^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo^http://sadl.org/RequestAggregator.sadl#rrm^http://sadl.org/RequestAggregator.sadl#RouteRequestMsg^http://sadl.org/RequestAggregator.sadl#receive1^http://sadl.org/RequestAggregator.sadl#ReqAggregator|)
                  (:display-name |vi of RouteRequestInfo of rrm of RouteRequestMsg of receive1 of ReqAggregator|)
                  (:SRL-names (|vi of rrm of RouteRequestMsg|))
                  (:direction monitored)
                  (:type list)
                  (:min-length 1)
                  (:max-length 10)
                  (:event-variable? nil)
                  )
                  ))
  )
)






