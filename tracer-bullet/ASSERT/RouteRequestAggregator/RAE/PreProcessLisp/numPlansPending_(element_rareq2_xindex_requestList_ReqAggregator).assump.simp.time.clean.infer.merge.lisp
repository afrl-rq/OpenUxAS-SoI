
(IN-PACKAGE "ACL2S")
(SET-IGNORE-OK T)
(DEFTTAG :PROGN!)
(DEFCONST *SRL-DATA-MINIMUM* (- (EXPT 2 31)))
(DEFCONST *SRL-DATA-MAXIMUM* (- (EXPT 2 31) 1))
(DEFDATA |translator generated name for rareq2_xindex|
         (RANGE INTEGER
          (*SRL-DATA-MINIMUM* <= _ <= *SRL-DATA-MAXIMUM*)))
(DEFDATA |translator generated name for translator_intermediate_variable_9 of requestList of ReqAggregator|
         '|http://sadl.org/RequestAggregator.sadl#RouteRequestInfo|)
(DEFFCONST
 |*translator generated name for translator_intermediate_variable_9 of requestList of ReqAggregator-VALUES*|
 '(|http://sadl.org/RequestAggregator.sadl#RouteRequestInfo|))
(DEFDATA |translator generated name for requestList of ReqAggregator|
         (LISTOF
          |translator generated name for translator_intermediate_variable_9 of requestList of ReqAggregator|))
(DEFUN |NTH-translator generated name for requestList of ReqAggregator-EnUm-InFer/ACC| (N
                                                                                        S)
  (DECLARE
   (XARGS :MODE :PROGRAM :GUARD
    (AND (NATP N) (UNSIGNED-BYTE-P 31 S))))
  (LET ((N (NTH-INTEGER-BETWEEN N 0 50)))
    (IF (<= N 0)
        (MV NIL S)
        (B* (((MV I S)
              (MV-LET (I SEED)
                      (DEFDATA::RANDOM-NATURAL-SEED S)
                      (MV (|NTH-translator generated name for translator_intermediate_variable_9 of requestList of ReqAggregator|
                           I)
                          (THE (UNSIGNED-BYTE 31) SEED))))
             ((MV L S)
              (|NTH-translator generated name for requestList of ReqAggregator-EnUm-InFer/ACC|
               (1- N) S)))
            (MV (CONS I L) S)))))
(DEFDATA-ATTACH
  |translator generated name for requestList of ReqAggregator|
  :ENUM/ACC
  |NTH-translator generated name for requestList of ReqAggregator-EnUm-InFer/ACC|)
(DEFDATA |translator generated name for previous numPlansPending of var22|
         (RANGE INTEGER
          (*SRL-DATA-MINIMUM* <= _ <= *SRL-DATA-MAXIMUM*)))
(DEFDATA |translator generated name for mID of var3|
         '|http://www.w3.org/2001/XMLSchema#string|)
(DEFFCONST |*translator generated name for mID of var3-VALUES*|
 '(|http://www.w3.org/2001/XMLSchema#string|))
(DEFFCONST |*translator generated name for mID of var3-VALS*|
 (QUOTE-ALL |*translator generated name for mID of var3-VALUES*|))
(DEFDATA |translator generated name for mID of RoutePlanGeneratedMsg of receive2 of ReqAggregator|
         '|http://www.w3.org/2001/XMLSchema#string|)
(DEFFCONST
 |*translator generated name for mID of RoutePlanGeneratedMsg of receive2 of ReqAggregator-VALUES*|
 '(|http://www.w3.org/2001/XMLSchema#string|))
(DEFFCONST
 |*translator generated name for mID of RoutePlanGeneratedMsg of receive2 of ReqAggregator-VALS*|
 (QUOTE-ALL
  |*translator generated name for mID of RoutePlanGeneratedMsg of receive2 of ReqAggregator-VALUES*|))
(DEFDATA |translator generated name for mID of var9|
         '|http://www.w3.org/2001/XMLSchema#string|)
(DEFFCONST |*translator generated name for mID of var9-VALUES*|
 '(|http://www.w3.org/2001/XMLSchema#string|))
(DEFFCONST |*translator generated name for mID of var9-VALS*|
 (QUOTE-ALL |*translator generated name for mID of var9-VALUES*|))
(DEFDATA |translator generated name for mID of VehiclePlanInfo of vpm of RoutePlanGeneratedMsg of receive2 of ReqAggregator|
         '|http://www.w3.org/2001/XMLSchema#string|)
(DEFFCONST
 |*translator generated name for mID of VehiclePlanInfo of vpm of RoutePlanGeneratedMsg of receive2 of ReqAggregator-VALUES*|
 '(|http://www.w3.org/2001/XMLSchema#string|))
(DEFFCONST
 |*translator generated name for mID of VehiclePlanInfo of vpm of RoutePlanGeneratedMsg of receive2 of ReqAggregator-VALS*|
 (QUOTE-ALL
  |*translator generated name for mID of VehiclePlanInfo of vpm of RoutePlanGeneratedMsg of receive2 of ReqAggregator-VALUES*|))
(DEFDATA |translator generated name for numPlansPending of (element rareq2_xindex of requestList of ReqAggregator)|
         (RANGE INTEGER
          (*SRL-DATA-MINIMUM* <= _ <= *SRL-DATA-MAXIMUM*)))
(REGISTER-SRL-NO-INNER-CONTINGENCY-VAR |event-variable|)
(REGISTER-SRL-NO-INNER-CONTINGENCY-VAR |mID of var3|)
(REGISTER-SRL-NO-INNER-CONTINGENCY-VAR
 |mID of RoutePlanGeneratedMsg of receive2 of ReqAggregator|)
(REGISTER-SRL-NO-INNER-CONTINGENCY-VAR |mID of var9|)
(REGISTER-SRL-NO-INNER-CONTINGENCY-VAR
 |mID of VehiclePlanInfo of vpm of RoutePlanGeneratedMsg of receive2 of ReqAggregator|)
(DEFLISTREQUIREMENT R3_INSTANCE_3
 ((|rareq2_xindex| |translator generated name for rareq2_xindexP|)
  (|requestList of ReqAggregator|
   |translator generated name for requestList of ReqAggregatorP|)
  (|previous numPlansPending of var22|
   |translator generated name for previous numPlansPending of var22P|)
  (|mID of var3| |translator generated name for mID of var3P|)
  (|mID of RoutePlanGeneratedMsg of receive2 of ReqAggregator|
   |translator generated name for mID of RoutePlanGeneratedMsg of receive2 of ReqAggregatorP|)
  (|mID of var9| |translator generated name for mID of var9P|)
  (|mID of VehiclePlanInfo of vpm of RoutePlanGeneratedMsg of receive2 of ReqAggregator|
   |translator generated name for mID of VehiclePlanInfo of vpm of RoutePlanGeneratedMsg of receive2 of ReqAggregatorP|))
 ((|numPlansPending of (element rareq2_xindex of requestList of ReqAggregator)|
   |translator generated name for numPlansPending of (element rareq2_xindex of requestList of ReqAggregator)P|))
 (RIMPLIES
  (AND (EQUAL |mID of var3|
              |mID of RoutePlanGeneratedMsg of receive2 of ReqAggregator|)
       (EQUAL |mID of var9|
              |mID of VehiclePlanInfo of vpm of RoutePlanGeneratedMsg of receive2 of ReqAggregator|))
  (EQUAL |numPlansPending of (element rareq2_xindex of requestList of ReqAggregator)|
         (- |previous numPlansPending of var22| 1))))