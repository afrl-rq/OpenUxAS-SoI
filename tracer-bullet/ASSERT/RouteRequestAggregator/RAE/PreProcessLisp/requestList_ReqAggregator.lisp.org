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

(defdata |translator_generated_name^translator_intermediate_variable_0^http://sadl.org/RequestAggregator.sadl#vi^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo^http://sadl.org/RequestAggregator.sadl#rrm^http://sadl.org/RequestAggregator.sadl#RouteRequestMsg^http://sadl.org/RequestAggregator.sadl#receive1^http://sadl.org/RequestAggregator.sadl#ReqAggregator| (enum '(|http://sadl.org/RequestAggregator.sadl#VehiclePlanInfo| )))
(defdata |translator_generated_name^http://sadl.org/RequestAggregator.sadl#vi^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo^http://sadl.org/RequestAggregator.sadl#rrm^http://sadl.org/RequestAggregator.sadl#RouteRequestMsg^http://sadl.org/RequestAggregator.sadl#receive1^http://sadl.org/RequestAggregator.sadl#ReqAggregator| (listof |translator_generated_name^translator_intermediate_variable_0^http://sadl.org/RequestAggregator.sadl#vi^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo^http://sadl.org/RequestAggregator.sadl#rrm^http://sadl.org/RequestAggregator.sadl#RouteRequestMsg^http://sadl.org/RequestAggregator.sadl#receive1^http://sadl.org/RequestAggregator.sadl#ReqAggregator|))
(displayname |translator_intermediate_variable_0^http://sadl.org/RequestAggregator.sadl#vi^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo^http://sadl.org/RequestAggregator.sadl#rrm^http://sadl.org/RequestAggregator.sadl#RouteRequestMsg^http://sadl.org/RequestAggregator.sadl#receive1^http://sadl.org/RequestAggregator.sadl#ReqAggregator| |translator_intermediate_variable_0 of vi of RouteRequestInfo of rrm of RouteRequestMsg of receive1 of ReqAggregator|)
(displayname |translator_intermediate_variable_0^http://sadl.org/RequestAggregator.sadl#vi^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo^http://sadl.org/RequestAggregator.sadl#rrm^http://sadl.org/RequestAggregator.sadl#RouteRequestMsg^http://sadl.org/RequestAggregator.sadl#receive1^http://sadl.org/RequestAggregator.sadl#ReqAggregatorP| |translator_intermediate_variable_0 of vi of RouteRequestInfo of rrm of RouteRequestMsg of receive1 of ReqAggregatorP|)
(displayname |translator_generated_name^translator_intermediate_variable_0^http://sadl.org/RequestAggregator.sadl#vi^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo^http://sadl.org/RequestAggregator.sadl#rrm^http://sadl.org/RequestAggregator.sadl#RouteRequestMsg^http://sadl.org/RequestAggregator.sadl#receive1^http://sadl.org/RequestAggregator.sadl#ReqAggregator| |translator generated name for translator_intermediate_variable_0 of vi of RouteRequestInfo of rrm of RouteRequestMsg of receive1 of ReqAggregator|)
(displayname |translator_generated_name^translator_intermediate_variable_0^http://sadl.org/RequestAggregator.sadl#vi^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo^http://sadl.org/RequestAggregator.sadl#rrm^http://sadl.org/RequestAggregator.sadl#RouteRequestMsg^http://sadl.org/RequestAggregator.sadl#receive1^http://sadl.org/RequestAggregator.sadl#ReqAggregatorP| |translator generated name for translator_intermediate_variable_0 of vi of RouteRequestInfo of rrm of RouteRequestMsg of receive1 of ReqAggregatorP|)
(displayname |http://sadl.org/RequestAggregator.sadl#vi^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo^http://sadl.org/RequestAggregator.sadl#rrm^http://sadl.org/RequestAggregator.sadl#RouteRequestMsg^http://sadl.org/RequestAggregator.sadl#receive1^http://sadl.org/RequestAggregator.sadl#ReqAggregator| |vi of RouteRequestInfo of rrm of RouteRequestMsg of receive1 of ReqAggregator|)
(displayname |http://sadl.org/RequestAggregator.sadl#vi^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo^http://sadl.org/RequestAggregator.sadl#rrm^http://sadl.org/RequestAggregator.sadl#RouteRequestMsg^http://sadl.org/RequestAggregator.sadl#receive1^http://sadl.org/RequestAggregator.sadl#ReqAggregatorP| |vi of RouteRequestInfo of rrm of RouteRequestMsg of receive1 of ReqAggregatorP|)
(displayname |translator_generated_name^http://sadl.org/RequestAggregator.sadl#vi^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo^http://sadl.org/RequestAggregator.sadl#rrm^http://sadl.org/RequestAggregator.sadl#RouteRequestMsg^http://sadl.org/RequestAggregator.sadl#receive1^http://sadl.org/RequestAggregator.sadl#ReqAggregator| |translator generated name for vi of RouteRequestInfo of rrm of RouteRequestMsg of receive1 of ReqAggregator|)
(displayname |translator_generated_name^http://sadl.org/RequestAggregator.sadl#vi^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo^http://sadl.org/RequestAggregator.sadl#rrm^http://sadl.org/RequestAggregator.sadl#RouteRequestMsg^http://sadl.org/RequestAggregator.sadl#receive1^http://sadl.org/RequestAggregator.sadl#ReqAggregatorP| |translator generated name for vi of RouteRequestInfo of rrm of RouteRequestMsg of receive1 of ReqAggregatorP|)

(defdata |translator_generated_name^translator_intermediate_variable_1^previous(http://sadl.org/RequestAggregator.sadl#requestList)^http://sadl.org/RequestAggregator.sadl#ReqAggregator| (enum '(|http://sadl.org/RequestAggregator.sadl#RouteRequestInfo| )))
(defdata |translator_generated_name^previous(http://sadl.org/RequestAggregator.sadl#requestList)^http://sadl.org/RequestAggregator.sadl#ReqAggregator| (listof |translator_generated_name^translator_intermediate_variable_1^previous(http://sadl.org/RequestAggregator.sadl#requestList)^http://sadl.org/RequestAggregator.sadl#ReqAggregator|))
(displayname |translator_intermediate_variable_1^previous(http://sadl.org/RequestAggregator.sadl#requestList)^http://sadl.org/RequestAggregator.sadl#ReqAggregator| |translator_intermediate_variable_1 of previous requestList of ReqAggregator|)
(displayname |translator_intermediate_variable_1^previous(http://sadl.org/RequestAggregator.sadl#requestList)^http://sadl.org/RequestAggregator.sadl#ReqAggregatorP| |translator_intermediate_variable_1 of previous requestList of ReqAggregatorP|)
(displayname |translator_generated_name^translator_intermediate_variable_1^previous(http://sadl.org/RequestAggregator.sadl#requestList)^http://sadl.org/RequestAggregator.sadl#ReqAggregator| |translator generated name for translator_intermediate_variable_1 of previous requestList of ReqAggregator|)
(displayname |translator_generated_name^translator_intermediate_variable_1^previous(http://sadl.org/RequestAggregator.sadl#requestList)^http://sadl.org/RequestAggregator.sadl#ReqAggregatorP| |translator generated name for translator_intermediate_variable_1 of previous requestList of ReqAggregatorP|)
(displayname |previous(http://sadl.org/RequestAggregator.sadl#requestList)^http://sadl.org/RequestAggregator.sadl#ReqAggregator| |previous requestList of ReqAggregator|)
(displayname |previous(http://sadl.org/RequestAggregator.sadl#requestList)^http://sadl.org/RequestAggregator.sadl#ReqAggregatorP| |previous requestList of ReqAggregatorP|)
(displayname |translator_generated_name^previous(http://sadl.org/RequestAggregator.sadl#requestList)^http://sadl.org/RequestAggregator.sadl#ReqAggregator| |translator generated name for previous requestList of ReqAggregator|)
(displayname |translator_generated_name^previous(http://sadl.org/RequestAggregator.sadl#requestList)^http://sadl.org/RequestAggregator.sadl#ReqAggregatorP| |translator generated name for previous requestList of ReqAggregatorP|)

(defdata |translator_generated_name^translator_intermediate_variable_2^http://sadl.org/RequestAggregator.sadl#requestList^http://sadl.org/RequestAggregator.sadl#ReqAggregator| (enum '(|http://sadl.org/RequestAggregator.sadl#RouteRequestInfo| )))
(defdata |translator_generated_name^http://sadl.org/RequestAggregator.sadl#requestList^http://sadl.org/RequestAggregator.sadl#ReqAggregator| (listof |translator_generated_name^translator_intermediate_variable_2^http://sadl.org/RequestAggregator.sadl#requestList^http://sadl.org/RequestAggregator.sadl#ReqAggregator|))
(displayname |translator_intermediate_variable_2^http://sadl.org/RequestAggregator.sadl#requestList^http://sadl.org/RequestAggregator.sadl#ReqAggregator| |translator_intermediate_variable_2 of requestList of ReqAggregator|)
(displayname |translator_intermediate_variable_2^http://sadl.org/RequestAggregator.sadl#requestList^http://sadl.org/RequestAggregator.sadl#ReqAggregatorP| |translator_intermediate_variable_2 of requestList of ReqAggregatorP|)
(displayname |translator_generated_name^translator_intermediate_variable_2^http://sadl.org/RequestAggregator.sadl#requestList^http://sadl.org/RequestAggregator.sadl#ReqAggregator| |translator generated name for translator_intermediate_variable_2 of requestList of ReqAggregator|)
(displayname |translator_generated_name^translator_intermediate_variable_2^http://sadl.org/RequestAggregator.sadl#requestList^http://sadl.org/RequestAggregator.sadl#ReqAggregatorP| |translator generated name for translator_intermediate_variable_2 of requestList of ReqAggregatorP|)
(displayname |http://sadl.org/RequestAggregator.sadl#requestList^http://sadl.org/RequestAggregator.sadl#ReqAggregator| |requestList of ReqAggregator|)
(displayname |http://sadl.org/RequestAggregator.sadl#requestList^http://sadl.org/RequestAggregator.sadl#ReqAggregatorP| |requestList of ReqAggregatorP|)
(displayname |translator_generated_name^http://sadl.org/RequestAggregator.sadl#requestList^http://sadl.org/RequestAggregator.sadl#ReqAggregator| |translator generated name for requestList of ReqAggregator|)
(displayname |translator_generated_name^http://sadl.org/RequestAggregator.sadl#requestList^http://sadl.org/RequestAggregator.sadl#ReqAggregatorP| |translator generated name for requestList of ReqAggregatorP|)

(defdata |translator_generated_name^http://sadl.org/RequestAggregator.sadl#mID^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo| (enum '(|http://www.w3.org/2001/XMLSchema#string| )))
(deffconst |*translator_generated_name^http://sadl.org/RequestAggregator.sadl#mID^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo-VALS*| (quote-all |*translator_generated_name^http://sadl.org/RequestAggregator.sadl#mID^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo-VALUES*|))
(displayname |http://sadl.org/RequestAggregator.sadl#mID^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo| |mID of RouteRequestInfo|)
(displayname |http://sadl.org/RequestAggregator.sadl#mID^http://sadl.org/RequestAggregator.sadl#RouteRequestInfoP| |mID of RouteRequestInfoP|)
(displayname |translator_generated_name^http://sadl.org/RequestAggregator.sadl#mID^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo| |translator generated name for mID of RouteRequestInfo|)
(displayname |translator_generated_name^http://sadl.org/RequestAggregator.sadl#mID^http://sadl.org/RequestAggregator.sadl#RouteRequestInfoP| |translator generated name for mID of RouteRequestInfoP|)
(displayname |*http://sadl.org/RequestAggregator.sadl#mID^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo-VALS*| |*mID of RouteRequestInfo-VALS*|)
(displayname |*http://sadl.org/RequestAggregator.sadl#mID^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo-VALUES*| |*mID of RouteRequestInfo-VALUES*|)
(displayname |*translator_generated_name^http://sadl.org/RequestAggregator.sadl#mID^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo-VALS*| |*translator generated name for mID of RouteRequestInfo-VALS*|)
(displayname |*translator_generated_name^http://sadl.org/RequestAggregator.sadl#mID^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo-VALUES*| |*translator generated name for mID of RouteRequestInfo-VALUES*|)

(defdata |translator_generated_name^http://sadl.org/RequestAggregator.sadl#numPlansPending^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo| (range integer (*SRL-data-minimum* <= _ <= *SRL-data-maximum*)))
(deffconst |*translator_generated_name^http://sadl.org/RequestAggregator.sadl#numPlansPending^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo-VALS*| (quote-all (gen-int-range *SRL-data-minimum* *SRL-data-maximum*)))
(displayname |http://sadl.org/RequestAggregator.sadl#numPlansPending^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo| |numPlansPending of RouteRequestInfo|)
(displayname |http://sadl.org/RequestAggregator.sadl#numPlansPending^http://sadl.org/RequestAggregator.sadl#RouteRequestInfoP| |numPlansPending of RouteRequestInfoP|)
(displayname |translator_generated_name^http://sadl.org/RequestAggregator.sadl#numPlansPending^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo| |translator generated name for numPlansPending of RouteRequestInfo|)
(displayname |translator_generated_name^http://sadl.org/RequestAggregator.sadl#numPlansPending^http://sadl.org/RequestAggregator.sadl#RouteRequestInfoP| |translator generated name for numPlansPending of RouteRequestInfoP|)
(displayname |*http://sadl.org/RequestAggregator.sadl#numPlansPending^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo-VALS*| |*numPlansPending of RouteRequestInfo-VALS*|)
(displayname |*http://sadl.org/RequestAggregator.sadl#numPlansPending^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo-VALUES*| |*numPlansPending of RouteRequestInfo-VALUES*|)
(displayname |*translator_generated_name^http://sadl.org/RequestAggregator.sadl#numPlansPending^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo-VALS*| |*translator generated name for numPlansPending of RouteRequestInfo-VALS*|)
(displayname |*translator_generated_name^http://sadl.org/RequestAggregator.sadl#numPlansPending^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo-VALUES*| |*translator generated name for numPlansPending of RouteRequestInfo-VALUES*|)

(defdata |translator_generated_name^translator_intermediate_variable_3^http://sadl.org/RequestAggregator.sadl#vi^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo| (enum '(|http://sadl.org/RequestAggregator.sadl#VehiclePlanInfo| )))
(defdata |translator_generated_name^http://sadl.org/RequestAggregator.sadl#vi^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo| (listof |translator_generated_name^translator_intermediate_variable_3^http://sadl.org/RequestAggregator.sadl#vi^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo|))
(displayname |translator_intermediate_variable_3^http://sadl.org/RequestAggregator.sadl#vi^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo| |translator_intermediate_variable_3 of vi of RouteRequestInfo|)
(displayname |translator_intermediate_variable_3^http://sadl.org/RequestAggregator.sadl#vi^http://sadl.org/RequestAggregator.sadl#RouteRequestInfoP| |translator_intermediate_variable_3 of vi of RouteRequestInfoP|)
(displayname |translator_generated_name^translator_intermediate_variable_3^http://sadl.org/RequestAggregator.sadl#vi^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo| |translator generated name for translator_intermediate_variable_3 of vi of RouteRequestInfo|)
(displayname |translator_generated_name^translator_intermediate_variable_3^http://sadl.org/RequestAggregator.sadl#vi^http://sadl.org/RequestAggregator.sadl#RouteRequestInfoP| |translator generated name for translator_intermediate_variable_3 of vi of RouteRequestInfoP|)
(displayname |http://sadl.org/RequestAggregator.sadl#vi^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo| |vi of RouteRequestInfo|)
(displayname |http://sadl.org/RequestAggregator.sadl#vi^http://sadl.org/RequestAggregator.sadl#RouteRequestInfoP| |vi of RouteRequestInfoP|)
(displayname |translator_generated_name^http://sadl.org/RequestAggregator.sadl#vi^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo| |translator generated name for vi of RouteRequestInfo|)
(displayname |translator_generated_name^http://sadl.org/RequestAggregator.sadl#vi^http://sadl.org/RequestAggregator.sadl#RouteRequestInfoP| |translator generated name for vi of RouteRequestInfoP|)

(defdata |translator_generated_name^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo| (enum '(|http://sadl.org/RequestAggregator.sadl#RouteRequestInfo|)))
(deffconst |*translator_generated_name^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo-VALS*| (quote-all |*translator_generated_name^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo-VALUES*|))
(defdecomposition |rareq_xxx|
((|inputvar1| |translator_generated_name^http://sadl.org/RequestAggregator.sadl#mID^http://sadl.org/RequestAggregator.sadl#RouteRequestInfoP|)
(|inputvar2| |translator_generated_name^http://sadl.org/RequestAggregator.sadl#numPlansPending^http://sadl.org/RequestAggregator.sadl#RouteRequestInfoP|)
(|inputvar3| |translator_generated_name^http://sadl.org/RequestAggregator.sadl#vi^http://sadl.org/RequestAggregator.sadl#RouteRequestInfoP|))
((|outputvar| |translator_generated_name^http://sadl.org/RequestAggregator.sadl#RouteRequestInfoP|)))

(deflistrequirement R1_instance_0
  (    (|http://sadl.org/RequestAggregator.sadl#mID^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo^http://sadl.org/RequestAggregator.sadl#rrm^http://sadl.org/RequestAggregator.sadl#RouteRequestMsg^http://sadl.org/RequestAggregator.sadl#receive1^http://sadl.org/RequestAggregator.sadl#ReqAggregator| |translator_generated_name^http://sadl.org/RequestAggregator.sadl#mID^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo^http://sadl.org/RequestAggregator.sadl#rrm^http://sadl.org/RequestAggregator.sadl#RouteRequestMsg^http://sadl.org/RequestAggregator.sadl#receive1^http://sadl.org/RequestAggregator.sadl#ReqAggregatorP|)
    (|http://sadl.org/RequestAggregator.sadl#vi^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo^http://sadl.org/RequestAggregator.sadl#rrm^http://sadl.org/RequestAggregator.sadl#RouteRequestMsg^http://sadl.org/RequestAggregator.sadl#receive1^http://sadl.org/RequestAggregator.sadl#ReqAggregator| |translator_generated_name^http://sadl.org/RequestAggregator.sadl#vi^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo^http://sadl.org/RequestAggregator.sadl#rrm^http://sadl.org/RequestAggregator.sadl#RouteRequestMsg^http://sadl.org/RequestAggregator.sadl#receive1^http://sadl.org/RequestAggregator.sadl#ReqAggregatorP|)
    (|previous(http://sadl.org/RequestAggregator.sadl#requestList)^http://sadl.org/RequestAggregator.sadl#ReqAggregator| |translator_generated_name^previous(http://sadl.org/RequestAggregator.sadl#requestList)^http://sadl.org/RequestAggregator.sadl#ReqAggregatorP|)
  )
  (    (|http://sadl.org/RequestAggregator.sadl#requestList^http://sadl.org/RequestAggregator.sadl#ReqAggregator| |translator_generated_name^http://sadl.org/RequestAggregator.sadl#requestList^http://sadl.org/RequestAggregator.sadl#ReqAggregatorP|)
  )
(rimplies T (equal |http://sadl.org/RequestAggregator.sadl#requestList^http://sadl.org/RequestAggregator.sadl#ReqAggregator| (snoc (|rareq_xxx| |http://sadl.org/RequestAggregator.sadl#mID^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo^http://sadl.org/RequestAggregator.sadl#rrm^http://sadl.org/RequestAggregator.sadl#RouteRequestMsg^http://sadl.org/RequestAggregator.sadl#receive1^http://sadl.org/RequestAggregator.sadl#ReqAggregator| (len-c |http://sadl.org/RequestAggregator.sadl#vi^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo^http://sadl.org/RequestAggregator.sadl#rrm^http://sadl.org/RequestAggregator.sadl#RouteRequestMsg^http://sadl.org/RequestAggregator.sadl#receive1^http://sadl.org/RequestAggregator.sadl#ReqAggregator|) |http://sadl.org/RequestAggregator.sadl#vi^http://sadl.org/RequestAggregator.sadl#RouteRequestInfo^http://sadl.org/RequestAggregator.sadl#rrm^http://sadl.org/RequestAggregator.sadl#RouteRequestMsg^http://sadl.org/RequestAggregator.sadl#receive1^http://sadl.org/RequestAggregator.sadl#ReqAggregator|) |previous(http://sadl.org/RequestAggregator.sadl#requestList)^http://sadl.org/RequestAggregator.sadl#ReqAggregator|))))

(SRL-meta-data 
  requirement-history 
  ((:SRL-name R1)
   (:Context 1)
   (:transformations ((grounding R1_instance_0)))
   (:RA-name R1_instance_0)
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
                  (:name |previous(http://sadl.org/RequestAggregator.sadl#requestList)^http://sadl.org/RequestAggregator.sadl#ReqAggregator|)
                  (:display-name |previous requestList of ReqAggregator|)
                  (:SRL-names (|previous requestList of ReqAggregator|))
                  (:direction monitored)
                  (:type list)
                  (:min-length :unspecified)
                  (:max-length :unspecified)
                  (:event-variable? nil)
                  (:no-contingency-checking? t)
                  )
                  (
                  (:name |http://sadl.org/RequestAggregator.sadl#requestList^http://sadl.org/RequestAggregator.sadl#ReqAggregator|)
                  (:display-name |requestList of ReqAggregator|)
                  (:SRL-names (|requestList of ReqAggregator|))
                  (:direction controlled)
                  (:type list)
                  (:min-length :unspecified)
                  (:max-length :unspecified)
                  (:event-variable? nil)
                  (:no-contingency-checking? t)
                  )))
  )
)

(SRL-meta-data 
  context 
  ((:context-id 1)
   (:exp (|ReqAggregator with receive1 RouteRequestMsg|))))


(defdata |translator_generated_name^rareq_xindex| (range integer (*SRL-data-minimum* <= _ <= *SRL-data-maximum*)))
(deffconst |*translator_generated_name^rareq_xindex-VALS*| (quote-all (gen-int-range *SRL-data-minimum* *SRL-data-maximum*)))
;(datavariable |rareq_xindex|)

(displayname |rareq_xindex| |rareq_xindex|)
(displayname |rareq_xindexP| |rareq_xindexP|)
(displayname |translator_generated_name^rareq_xindex| |translator generated name for rareq_xindex|)
(displayname |translator_generated_name^rareq_xindexP| |translator generated name for rareq_xindexP|)
(displayname |*rareq_xindex-VALS*| |*rareq_xindex-VALS*|)
(displayname |*rareq_xindex-VALUES*| |*rareq_xindex-VALUES*|)
(displayname |*translator_generated_name^rareq_xindex-VALS*| |*translator generated name for rareq_xindex-VALS*|)
(displayname |*translator_generated_name^rareq_xindex-VALUES*| |*translator generated name for rareq_xindex-VALUES*|)


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






(SRL-meta-data 
  no-contingency-checking-register 
  ((:name |translator_generated_name^previous(http://sadl.org/RequestAggregator.sadl#requestList)^http://sadl.org/RequestAggregator.sadl#ReqAggregator|)))

(SRL-meta-data 
  no-contingency-checking-register 
  ((:name |translator_generated_name^http://sadl.org/RequestAggregator.sadl#requestList^http://sadl.org/RequestAggregator.sadl#ReqAggregator|)))

