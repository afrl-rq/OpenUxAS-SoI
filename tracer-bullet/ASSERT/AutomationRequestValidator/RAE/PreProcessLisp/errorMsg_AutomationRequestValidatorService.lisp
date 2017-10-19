; Generated using ACL2s Translator Version 3.0.0.201709292107_java 
; and RCE SADL Feature 2.1.0.201709221328
(in-package "ACL2S")
(set-ignore-ok t)
(defttag :progn!)
(include-book "requirements-analyses-book")

(defdata |translator_generated_name^http://sadl.org/Validator.sadl#uxas__messages__task__TaskAutomationRequest| (enum '(|Validator.sadl_uxas__messages__task__TaskAutomationRequest_Val_1| )))
(SRL-meta-data
  data-definition
  ((:name |translator_generated_name^http://sadl.org/Validator.sadl#uxas__messages__task__TaskAutomationRequest|)
   (:display-name |uxas__messages__task__TaskAutomationRequest|)
   (:SRL-namespace |http://sadl.org/Validator.sadl|)
   (:SRL-classname |uxas__messages__task__TaskAutomationRequest|)
   (:Interface-definition? nil)
   (:SRL-property-name ())))

(defdata |translator_generated_name^http://sadl.org/Validator.sadl#ErrorMsg| (enum '(|http://sadl.org/Validator.sadl#ErrorMsgTooManyRequests| |http://sadl.org/Validator.sadl#ErrorMsgTimeout| )))
(SRL-meta-data
  data-definition
  ((:name |translator_generated_name^http://sadl.org/Validator.sadl#ErrorMsg|)
   (:display-name |ErrorMsg|)
   (:SRL-namespace |http://sadl.org/Validator.sadl|)
   (:SRL-classname |ErrorMsg|)
   (:Interface-definition? nil)
   (:SRL-property-name ())))

(defdata |translator_generated_name^LIST_OF_1_TO_1_http://sadl.org/Validator.sadl#uxas__messages__task__TaskAutomationRequest| (listof |translator_generated_name^http://sadl.org/Validator.sadl#uxas__messages__task__TaskAutomationRequest|) )
(SRL-meta-data
  data-definition
  ((:name |translator_generated_name^LIST_OF_1_TO_1_http://sadl.org/Validator.sadl#uxas__messages__task__TaskAutomationRequest|)
   (:display-name |LIST_OF_1_TO_1_uxas__messages__task__TaskAutomationRequest|)
   (:SRL-namespace |http://sadl.org/Validator.sadl|)
   (:SRL-classname |uxas__messages__task__TaskAutomationRequest|)
   (:Interface-definition? nil)
   (:SRL-property-name ())))

(SRL-meta-data
  list-type-length-data
  ((:name |translator_generated_name^LIST_OF_1_TO_1_http://sadl.org/Validator.sadl#uxas__messages__task__TaskAutomationRequest|)
   (:min-len 1)
   (:max-len 1)))
(defdata |translator_generated_name^http://www.w3.org/2001/XMLSchema#int_0_TO_20| (range integer (0 <= _ <= 20)))
(SRL-meta-data
  data-definition
  ((:name |translator_generated_name^http://www.w3.org/2001/XMLSchema#int_0_TO_20|)
   (:display-name |int_0_TO_20|)
   (:SRL-namespace |http://www.w3.org/2001/XMLSchema|)
   (:SRL-classname |int|)
   (:Interface-definition? nil)
   (:SRL-property-name ())))

(defdata |translator_generated_name^http://www.w3.org/2001/XMLSchema#boolean| (enum '(true false )))
(SRL-meta-data
  data-definition
  ((:name |translator_generated_name^http://www.w3.org/2001/XMLSchema#boolean|)
   (:display-name |boolean|)
   (:SRL-namespace |http://www.w3.org/2001/XMLSchema|)
   (:SRL-classname |boolean|)
   (:Interface-definition? nil)
   (:SRL-property-name ())))

(defdata |translator_generated_name^http://sadl.org/Validator.sadl#AutomationRequestValidatorServiceState| (enum '(|http://sadl.org/Validator.sadl#Idle| |http://sadl.org/Validator.sadl#Busy| )))
(SRL-meta-data
  data-definition
  ((:name |translator_generated_name^http://sadl.org/Validator.sadl#AutomationRequestValidatorServiceState|)
   (:display-name |AutomationRequestValidatorServiceState|)
   (:SRL-namespace |http://sadl.org/Validator.sadl|)
   (:SRL-classname |AutomationRequestValidatorServiceState|)
   (:Interface-definition? nil)
   (:SRL-property-name ())))

(defdata |translator_generated_name^http://www.w3.org/2001/XMLSchema#int_0_TO_11| (range integer (0 <= _ <= 11)))
(SRL-meta-data
  data-definition
  ((:name |translator_generated_name^http://www.w3.org/2001/XMLSchema#int_0_TO_11|)
   (:display-name |int_0_TO_11|)
   (:SRL-namespace |http://www.w3.org/2001/XMLSchema|)
   (:SRL-classname |int|)
   (:Interface-definition? nil)
   (:SRL-property-name ())))

(defdata |translator_generated_name^http://sadl.org/Validator.sadl#uxas__messages__task__UniqueAutomationResponse| (enum '(|Validator.sadl_uxas__messages__task__UniqueAutomationResponse_Val_1| )))
(SRL-meta-data
  data-definition
  ((:name |translator_generated_name^http://sadl.org/Validator.sadl#uxas__messages__task__UniqueAutomationResponse|)
   (:display-name |uxas__messages__task__UniqueAutomationResponse|)
   (:SRL-namespace |http://sadl.org/Validator.sadl|)
   (:SRL-classname |uxas__messages__task__UniqueAutomationResponse|)
   (:Interface-definition? nil)
   (:SRL-property-name ())))

(defdata |translator_generated_name^http://www.w3.org/2001/XMLSchema#int| (range integer (*SRL-data-minimum* <= _ <= *SRL-data-maximum*)))
(SRL-meta-data
  data-definition
  ((:name |translator_generated_name^http://www.w3.org/2001/XMLSchema#int|)
   (:display-name |int|)
   (:SRL-namespace |http://www.w3.org/2001/XMLSchema|)
   (:SRL-classname |int|)
   (:Interface-definition? nil)
   (:SRL-property-name ())))


(defdecomposition |http://sadl.org/ValidatorReq.sreq_DecompVar1|
()
((|http://sadl.org/Validator.sadl#uxas__messages__task__TaskAutomationRequest| |translator_generated_name^http://sadl.org/Validator.sadl#uxas__messages__task__TaskAutomationRequestP|)))

(deflistrequirement |AutomationRequestReceived2_instance_4|
  (    (|previous(http://sadl.org/Validator.sadl#state^http://sadl.org/Validator.sadl#AutomationRequestValidatorService)| |translator_generated_name^http://sadl.org/Validator.sadl#AutomationRequestValidatorServiceStateP|)
       (|http://sadl.org/Validator.sadl#uxas__messages__task__TaskAutomationRequest__Subscription^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| |translator_generated_name^http://sadl.org/Validator.sadl#uxas__messages__task__TaskAutomationRequestP|)
       (|http://sadl.org/Validator.sadl#automationRequestList^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| |translator_generated_name^LIST_OF_1_TO_1_http://sadl.org/Validator.sadl#uxas__messages__task__TaskAutomationRequestP|)
       (|http://sadl.org/Validator.sadl#maxListLength^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| |translator_generated_name^http://www.w3.org/2001/XMLSchema#int_0_TO_20P|)  )
  (    (|http://sadl.org/Validator.sadl#errorMsg^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| |translator_generated_name^http://sadl.org/Validator.sadl#ErrorMsgP|)  )
(rimplies (and (not (equal |previous(http://sadl.org/Validator.sadl#state^http://sadl.org/Validator.sadl#AutomationRequestValidatorService)| '|http://sadl.org/Validator.sadl#Busy|)) (and (equal |http://sadl.org/Validator.sadl#uxas__messages__task__TaskAutomationRequest__Subscription^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| (|http://sadl.org/ValidatorReq.sreq_DecompVar1|)) (equal (len-c  |http://sadl.org/Validator.sadl#automationRequestList^http://sadl.org/Validator.sadl#AutomationRequestValidatorService|) |http://sadl.org/Validator.sadl#maxListLength^http://sadl.org/Validator.sadl#AutomationRequestValidatorService|))) (equal |http://sadl.org/Validator.sadl#errorMsg^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| '|http://sadl.org/Validator.sadl#ErrorMsgTooManyRequests|)))

(SRL-meta-data 
  requirement-history 
  ((:SRL-name |AutomationRequestReceived2|)
   (:Context 1)
   (:transformations ((grounding AutomationRequestReceived2_instance_3)(normalization body AutomationRequestReceived2_instance_3)))
   (:RA-name |AutomationRequestReceived2_instance_4|)
   (:ModelGenFile "")
   (:VarMapFile "")
      (:Variables ((
                  (:name |previous(http://sadl.org/Validator.sadl#state^http://sadl.org/Validator.sadl#AutomationRequestValidatorService)|)
                  (:display-name |previous state of AutomationRequestValidatorService|)
                  (:SRL-names (|previous state of AutomationRequestValidatorService|))
                  (:direction monitored)
                  (:type enum)
                  (:event-variable? nil)
                  (:no-contingency-checking? t)
                  )
                  (
                  (:name |http://sadl.org/Validator.sadl#uxas__messages__task__TaskAutomationRequest__Subscription^http://sadl.org/Validator.sadl#AutomationRequestValidatorService|)
                  (:display-name |uxas__messages__task__TaskAutomationRequest__Subscription of AutomationRequestValidatorService|)
                  (:SRL-names (|uxas__messages__task__TaskAutomationRequest__Subscription of AutomationRequestValidatorService|))
                  (:direction monitored)
                  (:type enum)
                  (:event-variable? nil)
                  (:no-contingency-checking? nil)
                  )
                  (
                (:name |http://sadl.org/Validator.sadl#automationRequestList^http://sadl.org/Validator.sadl#AutomationRequestValidatorService|)
                (:display-name |automationRequestList of AutomationRequestValidatorService|)
                (:SRL-names (|automationRequestList of AutomationRequestValidatorService|))
                (:direction monitored)
                (:type list)
                (:min-length 1)
                (:max-length 1)
                (:event-variable? nil)
                )
                  (
                  (:name |http://sadl.org/Validator.sadl#maxListLength^http://sadl.org/Validator.sadl#AutomationRequestValidatorService|)
                  (:display-name |maxListLength of AutomationRequestValidatorService|)
                  (:SRL-names (|maxListLength of AutomationRequestValidatorService|))
                  (:direction monitored)
                  (:type int)
                  (:functional-max 20)
                  (:functional-min 0)
                  (:tolerance 1)
                  (:resolution 1)
                  (:event-variable? nil)
                  (:no-contingency-checking? nil)
                  )
                  (
                  (:name |http://sadl.org/Validator.sadl#errorMsg^http://sadl.org/Validator.sadl#AutomationRequestValidatorService|)
                  (:display-name |errorMsg of AutomationRequestValidatorService|)
                  (:SRL-names (|errorMsg of AutomationRequestValidatorService|))
                  (:direction controlled)
                  (:type enum)
                  (:event-variable? nil)
                  (:no-contingency-checking? t)
                  )))
  )
)

(deflistrequirement |AutomationRequestReceived2_instance_5|
  (    (|http://sadl.org/Validator.sadl#uxas__messages__task__TaskAutomationRequest__Subscription^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| |translator_generated_name^http://sadl.org/Validator.sadl#uxas__messages__task__TaskAutomationRequestP|)
       (|http://sadl.org/Validator.sadl#automationRequestList^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| |translator_generated_name^LIST_OF_1_TO_1_http://sadl.org/Validator.sadl#uxas__messages__task__TaskAutomationRequestP|)
       (|http://sadl.org/Validator.sadl#maxListLength^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| |translator_generated_name^http://www.w3.org/2001/XMLSchema#int_0_TO_20P|)
       (|http://sadl.org/Validator.sadl#timeSinceLastTimerUpdate^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| |translator_generated_name^http://www.w3.org/2001/XMLSchema#int_0_TO_11P|)
       (|http://sadl.org/Validator.sadl#uxas__messages__task__UniqueAutomationResponse__Subscription^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| |translator_generated_name^http://sadl.org/Validator.sadl#uxas__messages__task__UniqueAutomationResponseP|)  )
  (    (|http://sadl.org/Validator.sadl#errorMsg^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| |translator_generated_name^http://sadl.org/Validator.sadl#ErrorMsgP|)  )
(rimplies (and (equal |http://sadl.org/Validator.sadl#uxas__messages__task__TaskAutomationRequest__Subscription^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| (|http://sadl.org/ValidatorReq.sreq_DecompVar1|)) (and (equal (len-c  |http://sadl.org/Validator.sadl#automationRequestList^http://sadl.org/Validator.sadl#AutomationRequestValidatorService|) |http://sadl.org/Validator.sadl#maxListLength^http://sadl.org/Validator.sadl#AutomationRequestValidatorService|) (and (srl-< |http://sadl.org/Validator.sadl#timeSinceLastTimerUpdate^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| 10) (equal |http://sadl.org/Validator.sadl#uxas__messages__task__UniqueAutomationResponse__Subscription^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| '|http://sadl.org/Validator.sadl#uxas__messages__task__UniqueAutomationResponse|)))) (equal |http://sadl.org/Validator.sadl#errorMsg^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| '|http://sadl.org/Validator.sadl#ErrorMsgTooManyRequests|)))

(SRL-meta-data 
  requirement-history 
  ((:SRL-name |AutomationRequestReceived2|)
   (:Context 1)
   (:transformations ((grounding AutomationRequestReceived2_instance_3)(normalization body AutomationRequestReceived2_instance_3)))
   (:RA-name |AutomationRequestReceived2_instance_5|)
   (:ModelGenFile "")
   (:VarMapFile "")
      (:Variables ((
                  (:name |http://sadl.org/Validator.sadl#uxas__messages__task__TaskAutomationRequest__Subscription^http://sadl.org/Validator.sadl#AutomationRequestValidatorService|)
                  (:display-name |uxas__messages__task__TaskAutomationRequest__Subscription of AutomationRequestValidatorService|)
                  (:SRL-names (|uxas__messages__task__TaskAutomationRequest__Subscription of AutomationRequestValidatorService|))
                  (:direction monitored)
                  (:type enum)
                  (:event-variable? nil)
                  (:no-contingency-checking? nil)
                  )
                  (
                (:name |http://sadl.org/Validator.sadl#automationRequestList^http://sadl.org/Validator.sadl#AutomationRequestValidatorService|)
                (:display-name |automationRequestList of AutomationRequestValidatorService|)
                (:SRL-names (|automationRequestList of AutomationRequestValidatorService|))
                (:direction monitored)
                (:type list)
                (:min-length 1)
                (:max-length 1)
                (:event-variable? nil)
                )
                  (
                  (:name |http://sadl.org/Validator.sadl#maxListLength^http://sadl.org/Validator.sadl#AutomationRequestValidatorService|)
                  (:display-name |maxListLength of AutomationRequestValidatorService|)
                  (:SRL-names (|maxListLength of AutomationRequestValidatorService|))
                  (:direction monitored)
                  (:type int)
                  (:functional-max 20)
                  (:functional-min 0)
                  (:tolerance 1)
                  (:resolution 1)
                  (:event-variable? nil)
                  (:no-contingency-checking? nil)
                  )
                  (
                  (:name |http://sadl.org/Validator.sadl#timeSinceLastTimerUpdate^http://sadl.org/Validator.sadl#AutomationRequestValidatorService|)
                  (:display-name |timeSinceLastTimerUpdate of AutomationRequestValidatorService|)
                  (:SRL-names (|timeSinceLastTimerUpdate of AutomationRequestValidatorService|))
                  (:direction monitored)
                  (:type int)
                  (:functional-max 11)
                  (:functional-min 0)
                  (:tolerance 1)
                  (:resolution 1)
                  (:event-variable? nil)
                  (:no-contingency-checking? nil)
                  )
                  (
                  (:name |http://sadl.org/Validator.sadl#uxas__messages__task__UniqueAutomationResponse__Subscription^http://sadl.org/Validator.sadl#AutomationRequestValidatorService|)
                  (:display-name |uxas__messages__task__UniqueAutomationResponse__Subscription of AutomationRequestValidatorService|)
                  (:SRL-names (|uxas__messages__task__UniqueAutomationResponse__Subscription of AutomationRequestValidatorService|))
                  (:direction monitored)
                  (:type enum)
                  (:event-variable? nil)
                  (:no-contingency-checking? t)
                  )
                  (
                  (:name |http://sadl.org/Validator.sadl#errorMsg^http://sadl.org/Validator.sadl#AutomationRequestValidatorService|)
                  (:display-name |errorMsg of AutomationRequestValidatorService|)
                  (:SRL-names (|errorMsg of AutomationRequestValidatorService|))
                  (:direction controlled)
                  (:type enum)
                  (:event-variable? nil)
                  (:no-contingency-checking? t)
                  )))
  )
)

(deflistrequirement |AutomationRequestReceived2_instance_6|
  (    (|previous(http://sadl.org/Validator.sadl#state^http://sadl.org/Validator.sadl#AutomationRequestValidatorService)| |translator_generated_name^http://sadl.org/Validator.sadl#AutomationRequestValidatorServiceStateP|)
       (|http://sadl.org/Validator.sadl#uxas__messages__task__TaskAutomationRequest__Subscription^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| |translator_generated_name^http://sadl.org/Validator.sadl#uxas__messages__task__TaskAutomationRequestP|)
       (|http://sadl.org/Validator.sadl#denialOfService^http://sadl.org/Validator.sadl#System| |translator_generated_name^http://www.w3.org/2001/XMLSchema#booleanP|)  )
  (    (|http://sadl.org/Validator.sadl#errorMsg^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| |translator_generated_name^http://sadl.org/Validator.sadl#ErrorMsgP|)  )
(rimplies (and (not (equal |previous(http://sadl.org/Validator.sadl#state^http://sadl.org/Validator.sadl#AutomationRequestValidatorService)| '|http://sadl.org/Validator.sadl#Busy|)) (and (equal |http://sadl.org/Validator.sadl#uxas__messages__task__TaskAutomationRequest__Subscription^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| (|http://sadl.org/ValidatorReq.sreq_DecompVar1|)) (equal |http://sadl.org/Validator.sadl#denialOfService^http://sadl.org/Validator.sadl#System| 'true))) (equal |http://sadl.org/Validator.sadl#errorMsg^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| '|http://sadl.org/Validator.sadl#ErrorMsgTooManyRequests|)))

(SRL-meta-data 
  requirement-history 
  ((:SRL-name |AutomationRequestReceived2|)
   (:Context 1)
   (:transformations ((grounding AutomationRequestReceived2_instance_3)(normalization body AutomationRequestReceived2_instance_3)))
   (:RA-name |AutomationRequestReceived2_instance_6|)
   (:ModelGenFile "")
   (:VarMapFile "")
      (:Variables ((
                  (:name |previous(http://sadl.org/Validator.sadl#state^http://sadl.org/Validator.sadl#AutomationRequestValidatorService)|)
                  (:display-name |previous state of AutomationRequestValidatorService|)
                  (:SRL-names (|previous state of AutomationRequestValidatorService|))
                  (:direction monitored)
                  (:type enum)
                  (:event-variable? nil)
                  (:no-contingency-checking? t)
                  )
                  (
                  (:name |http://sadl.org/Validator.sadl#uxas__messages__task__TaskAutomationRequest__Subscription^http://sadl.org/Validator.sadl#AutomationRequestValidatorService|)
                  (:display-name |uxas__messages__task__TaskAutomationRequest__Subscription of AutomationRequestValidatorService|)
                  (:SRL-names (|uxas__messages__task__TaskAutomationRequest__Subscription of AutomationRequestValidatorService|))
                  (:direction monitored)
                  (:type enum)
                  (:event-variable? nil)
                  (:no-contingency-checking? nil)
                  )
                  (
                  (:name |http://sadl.org/Validator.sadl#denialOfService^http://sadl.org/Validator.sadl#System|)
                  (:display-name |denialOfService of System|)
                  (:SRL-names (|denialOfService of System|))
                  (:direction monitored)
                  (:type boolean)
                  (:event-variable? nil)
                  (:no-contingency-checking? nil)
                  )
                  (
                  (:name |http://sadl.org/Validator.sadl#errorMsg^http://sadl.org/Validator.sadl#AutomationRequestValidatorService|)
                  (:display-name |errorMsg of AutomationRequestValidatorService|)
                  (:SRL-names (|errorMsg of AutomationRequestValidatorService|))
                  (:direction controlled)
                  (:type enum)
                  (:event-variable? nil)
                  (:no-contingency-checking? t)
                  )))
  )
)

(deflistrequirement |AutomationRequestReceived2_instance_7|
  (    (|http://sadl.org/Validator.sadl#uxas__messages__task__TaskAutomationRequest__Subscription^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| |translator_generated_name^http://sadl.org/Validator.sadl#uxas__messages__task__TaskAutomationRequestP|)
       (|http://sadl.org/Validator.sadl#denialOfService^http://sadl.org/Validator.sadl#System| |translator_generated_name^http://www.w3.org/2001/XMLSchema#booleanP|)
       (|http://sadl.org/Validator.sadl#timeSinceLastTimerUpdate^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| |translator_generated_name^http://www.w3.org/2001/XMLSchema#int_0_TO_11P|)
       (|http://sadl.org/Validator.sadl#uxas__messages__task__UniqueAutomationResponse__Subscription^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| |translator_generated_name^http://sadl.org/Validator.sadl#uxas__messages__task__UniqueAutomationResponseP|)  )
  (    (|http://sadl.org/Validator.sadl#errorMsg^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| |translator_generated_name^http://sadl.org/Validator.sadl#ErrorMsgP|)  )
(rimplies (and (equal |http://sadl.org/Validator.sadl#uxas__messages__task__TaskAutomationRequest__Subscription^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| (|http://sadl.org/ValidatorReq.sreq_DecompVar1|)) (and (equal |http://sadl.org/Validator.sadl#denialOfService^http://sadl.org/Validator.sadl#System| 'true) (and (srl-< |http://sadl.org/Validator.sadl#timeSinceLastTimerUpdate^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| 10) (equal |http://sadl.org/Validator.sadl#uxas__messages__task__UniqueAutomationResponse__Subscription^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| '|http://sadl.org/Validator.sadl#uxas__messages__task__UniqueAutomationResponse|)))) (equal |http://sadl.org/Validator.sadl#errorMsg^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| '|http://sadl.org/Validator.sadl#ErrorMsgTooManyRequests|)))

(SRL-meta-data 
  requirement-history 
  ((:SRL-name |AutomationRequestReceived2|)
   (:Context 1)
   (:transformations ((grounding AutomationRequestReceived2_instance_3)(normalization body AutomationRequestReceived2_instance_3)))
   (:RA-name |AutomationRequestReceived2_instance_7|)
   (:ModelGenFile "")
   (:VarMapFile "")
      (:Variables ((
                  (:name |http://sadl.org/Validator.sadl#uxas__messages__task__TaskAutomationRequest__Subscription^http://sadl.org/Validator.sadl#AutomationRequestValidatorService|)
                  (:display-name |uxas__messages__task__TaskAutomationRequest__Subscription of AutomationRequestValidatorService|)
                  (:SRL-names (|uxas__messages__task__TaskAutomationRequest__Subscription of AutomationRequestValidatorService|))
                  (:direction monitored)
                  (:type enum)
                  (:event-variable? nil)
                  (:no-contingency-checking? nil)
                  )
                  (
                  (:name |http://sadl.org/Validator.sadl#denialOfService^http://sadl.org/Validator.sadl#System|)
                  (:display-name |denialOfService of System|)
                  (:SRL-names (|denialOfService of System|))
                  (:direction monitored)
                  (:type boolean)
                  (:event-variable? nil)
                  (:no-contingency-checking? nil)
                  )
                  (
                  (:name |http://sadl.org/Validator.sadl#timeSinceLastTimerUpdate^http://sadl.org/Validator.sadl#AutomationRequestValidatorService|)
                  (:display-name |timeSinceLastTimerUpdate of AutomationRequestValidatorService|)
                  (:SRL-names (|timeSinceLastTimerUpdate of AutomationRequestValidatorService|))
                  (:direction monitored)
                  (:type int)
                  (:functional-max 11)
                  (:functional-min 0)
                  (:tolerance 1)
                  (:resolution 1)
                  (:event-variable? nil)
                  (:no-contingency-checking? nil)
                  )
                  (
                  (:name |http://sadl.org/Validator.sadl#uxas__messages__task__UniqueAutomationResponse__Subscription^http://sadl.org/Validator.sadl#AutomationRequestValidatorService|)
                  (:display-name |uxas__messages__task__UniqueAutomationResponse__Subscription of AutomationRequestValidatorService|)
                  (:SRL-names (|uxas__messages__task__UniqueAutomationResponse__Subscription of AutomationRequestValidatorService|))
                  (:direction monitored)
                  (:type enum)
                  (:event-variable? nil)
                  (:no-contingency-checking? t)
                  )
                  (
                  (:name |http://sadl.org/Validator.sadl#errorMsg^http://sadl.org/Validator.sadl#AutomationRequestValidatorService|)
                  (:display-name |errorMsg of AutomationRequestValidatorService|)
                  (:SRL-names (|errorMsg of AutomationRequestValidatorService|))
                  (:direction controlled)
                  (:type enum)
                  (:event-variable? nil)
                  (:no-contingency-checking? t)
                  )))
  )
)

(defrequirement |Timeout_instance_23|
  (    (|previous(http://sadl.org/Validator.sadl#state^http://sadl.org/Validator.sadl#AutomationRequestValidatorService)| |translator_generated_name^http://sadl.org/Validator.sadl#AutomationRequestValidatorServiceStateP|)
       (|previous(http://sadl.org/Validator.sadl#timeSinceLastTimerUpdate^http://sadl.org/Validator.sadl#AutomationRequestValidatorService)| |translator_generated_name^http://www.w3.org/2001/XMLSchema#intP|)
       (|http://sadl.org/Validator.sadl#uxas__messages__task__UniqueAutomationResponse__Subscription^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| |translator_generated_name^http://sadl.org/Validator.sadl#uxas__messages__task__UniqueAutomationResponseP|)  )
  (    (|http://sadl.org/Validator.sadl#errorMsg^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| |translator_generated_name^http://sadl.org/Validator.sadl#ErrorMsgP|)  )
(rimplies (and (equal |previous(http://sadl.org/Validator.sadl#state^http://sadl.org/Validator.sadl#AutomationRequestValidatorService)| '|http://sadl.org/Validator.sadl#Busy|) (or (srl->= |previous(http://sadl.org/Validator.sadl#timeSinceLastTimerUpdate^http://sadl.org/Validator.sadl#AutomationRequestValidatorService)| 10) (not (equal |http://sadl.org/Validator.sadl#uxas__messages__task__UniqueAutomationResponse__Subscription^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| '|http://sadl.org/Validator.sadl#uxas__messages__task__UniqueAutomationResponse|)))) (equal |http://sadl.org/Validator.sadl#errorMsg^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| '|http://sadl.org/Validator.sadl#ErrorMsgTimeout|)))

(SRL-meta-data 
  requirement-history 
  ((:SRL-name |Timeout|)
   (:Context 1)
   (:transformations ((grounding Timeout_instance_23)))
   (:RA-name |Timeout_instance_23|)
   (:ModelGenFile "")
   (:VarMapFile "")
      (:Variables ((
                  (:name |previous(http://sadl.org/Validator.sadl#state^http://sadl.org/Validator.sadl#AutomationRequestValidatorService)|)
                  (:display-name |previous state of AutomationRequestValidatorService|)
                  (:SRL-names (|previous state of AutomationRequestValidatorService|))
                  (:direction monitored)
                  (:type enum)
                  (:event-variable? nil)
                  (:no-contingency-checking? t)
                  )
                  (
                  (:name |previous(http://sadl.org/Validator.sadl#timeSinceLastTimerUpdate^http://sadl.org/Validator.sadl#AutomationRequestValidatorService)|)
                  (:display-name |previous timeSinceLastTimerUpdate of AutomationRequestValidatorService|)
                  (:SRL-names (|previous timeSinceLastTimerUpdate of AutomationRequestValidatorService|))
                  (:direction monitored)
                  (:type int)
                  (:functional-max :unspecified)
                  (:functional-min :unspecified)
                  (:tolerance :unspecified)
                  (:resolution :unspecified)
                  (:event-variable? nil)
                  (:no-contingency-checking? nil)
                  )
                  (
                  (:name |http://sadl.org/Validator.sadl#uxas__messages__task__UniqueAutomationResponse__Subscription^http://sadl.org/Validator.sadl#AutomationRequestValidatorService|)
                  (:display-name |uxas__messages__task__UniqueAutomationResponse__Subscription of AutomationRequestValidatorService|)
                  (:SRL-names (|uxas__messages__task__UniqueAutomationResponse__Subscription of AutomationRequestValidatorService|))
                  (:direction monitored)
                  (:type enum)
                  (:event-variable? nil)
                  (:no-contingency-checking? t)
                  )
                  (
                  (:name |http://sadl.org/Validator.sadl#errorMsg^http://sadl.org/Validator.sadl#AutomationRequestValidatorService|)
                  (:display-name |errorMsg of AutomationRequestValidatorService|)
                  (:SRL-names (|errorMsg of AutomationRequestValidatorService|))
                  (:direction controlled)
                  (:type enum)
                  (:event-variable? nil)
                  (:no-contingency-checking? t)
                  )))
  )
)


(defimmaterial |A4_instance_37|
  (    (|http://sadl.org/Validator.sadl#uxas__messages__task__TaskAutomationRequest__Subscription^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| |translator_generated_name^http://sadl.org/Validator.sadl#uxas__messages__task__TaskAutomationRequestP|)
       (|http://sadl.org/Validator.sadl#automationRequestList^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| |translator_generated_name^LIST_OF_1_TO_1_http://sadl.org/Validator.sadl#uxas__messages__task__TaskAutomationRequestP|)
       (|http://sadl.org/Validator.sadl#maxListLength^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| |translator_generated_name^http://www.w3.org/2001/XMLSchema#int_0_TO_20P|)
       (|http://sadl.org/Validator.sadl#denialOfService^http://sadl.org/Validator.sadl#System| |translator_generated_name^http://www.w3.org/2001/XMLSchema#booleanP|)  )
  (    (|http://sadl.org/Validator.sadl#errorMsg^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| |translator_generated_name^http://sadl.org/Validator.sadl#ErrorMsgP|)  )
(not (and (equal |http://sadl.org/Validator.sadl#uxas__messages__task__TaskAutomationRequest__Subscription^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| (|http://sadl.org/ValidatorReq.sreq_DecompVar3|)) (or (equal (len-c  |http://sadl.org/Validator.sadl#automationRequestList^http://sadl.org/Validator.sadl#AutomationRequestValidatorService|) |http://sadl.org/Validator.sadl#maxListLength^http://sadl.org/Validator.sadl#AutomationRequestValidatorService|) (equal |http://sadl.org/Validator.sadl#denialOfService^http://sadl.org/Validator.sadl#System| 'true)))))

(SRL-meta-data 
  immaterial-history
  ((:SRL-name |A4|)
   (:context 1)
   (:transformations ((grounding A4_instance_37)))
   (:Assertion-name |A4_instance_37|)
      (:Variables ((
                  (:name |http://sadl.org/Validator.sadl#errorMsg^http://sadl.org/Validator.sadl#AutomationRequestValidatorService|)
                  (:display-name |errorMsg of AutomationRequestValidatorService|)
                  (:SRL-names (|errorMsg of AutomationRequestValidatorService|))
                  (:direction controlled)
                  (:type enum)
                  (:event-variable? nil)
                  (:no-contingency-checking? nil)
                  )
                  (
                  (:name |http://sadl.org/Validator.sadl#uxas__messages__task__TaskAutomationRequest__Subscription^http://sadl.org/Validator.sadl#AutomationRequestValidatorService|)
                  (:display-name |uxas__messages__task__TaskAutomationRequest__Subscription of AutomationRequestValidatorService|)
                  (:SRL-names (|uxas__messages__task__TaskAutomationRequest__Subscription of AutomationRequestValidatorService|))
                  (:direction monitored)
                  (:type enum)
                  (:event-variable? nil)
                  (:no-contingency-checking? nil)
                  )
                  (
                (:name |http://sadl.org/Validator.sadl#automationRequestList^http://sadl.org/Validator.sadl#AutomationRequestValidatorService|)
                (:display-name |automationRequestList of AutomationRequestValidatorService|)
                (:SRL-names (|automationRequestList of AutomationRequestValidatorService|))
                (:direction monitored)
                (:type list)
                (:min-length 1)
                (:max-length 1)
                (:event-variable? nil)
                )
                  (
                  (:name |http://sadl.org/Validator.sadl#maxListLength^http://sadl.org/Validator.sadl#AutomationRequestValidatorService|)
                  (:display-name |maxListLength of AutomationRequestValidatorService|)
                  (:SRL-names (|maxListLength of AutomationRequestValidatorService|))
                  (:direction monitored)
                  (:type int)
                  (:functional-max 20)
                  (:functional-min 0)
                  (:tolerance 1)
                  (:resolution 1)
                  (:event-variable? nil)
                  (:no-contingency-checking? nil)
                  )
                  (
                  (:name |http://sadl.org/Validator.sadl#denialOfService^http://sadl.org/Validator.sadl#System|)
                  (:display-name |denialOfService of System|)
                  (:SRL-names (|denialOfService of System|))
                  (:direction monitored)
                  (:type boolean)
                  (:event-variable? nil)
                  (:no-contingency-checking? nil)
                  )))
  )
)



(SRL-meta-data 
  constant
  ((:name |Validator.sadl_uxas__messages__task__TaskAutomationRequest_Val_1|)
   (:display-name |Validator.sadl_uxas__messages__task__TaskAutomationRequest_Val_1|)
   (:SRL-name |Validator.sadl_uxas__messages__task__TaskAutomationRequest_Val_1|)))

(SRL-meta-data 
  constant
  ((:name |http://sadl.org/Validator.sadl#ErrorMsgTooManyRequests|)
   (:display-name |ErrorMsgTooManyRequests|)
   (:SRL-name |ErrorMsgTooManyRequests|)))

(SRL-meta-data 
  constant
  ((:name |http://sadl.org/Validator.sadl#ErrorMsgTimeout|)
   (:display-name |ErrorMsgTimeout|)
   (:SRL-name |ErrorMsgTimeout|)))

(SRL-meta-data 
  constant
  ((:name |true|)
   (:display-name |true|)
   (:SRL-name |true|)))

(SRL-meta-data 
  constant
  ((:name |false|)
   (:display-name |false|)
   (:SRL-name |false|)))

(SRL-meta-data 
  constant
  ((:name |http://sadl.org/Validator.sadl#Idle|)
   (:display-name |Idle|)
   (:SRL-name |Idle|)))

(SRL-meta-data 
  constant
  ((:name |http://sadl.org/Validator.sadl#Busy|)
   (:display-name |Busy|)
   (:SRL-name |Busy|)))

(SRL-meta-data 
  constant
  ((:name |Validator.sadl_uxas__messages__task__UniqueAutomationResponse_Val_1|)
   (:display-name |Validator.sadl_uxas__messages__task__UniqueAutomationResponse_Val_1|)
   (:SRL-name |Validator.sadl_uxas__messages__task__UniqueAutomationResponse_Val_1|)))


(SRL-meta-data 
  no-contingency-checking-register
  ((:name |translator_generated_name^http://sadl.org/Validator.sadl#ErrorMsg|)))

(SRL-meta-data 
  no-contingency-checking-register
  ((:name |translator_generated_name^http://sadl.org/Validator.sadl#AutomationRequestValidatorServiceState|)))

(SRL-meta-data 
  no-contingency-checking-register
  ((:name |translator_generated_name^http://sadl.org/Validator.sadl#uxas__messages__task__UniqueAutomationResponse|)))


(SRL-meta-data 
  context 
  ((:context-id 1)
   (:exp (|true|))))

