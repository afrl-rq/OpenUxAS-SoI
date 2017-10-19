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
(defdata |translator_generated_name^http://sadl.org/Validator.sadl#AutomationRequestValidatorServiceState| (enum '(|http://sadl.org/Validator.sadl#Idle| |http://sadl.org/Validator.sadl#Busy| )))
(SRL-meta-data
  data-definition
  ((:name |translator_generated_name^http://sadl.org/Validator.sadl#AutomationRequestValidatorServiceState|)
   (:display-name |AutomationRequestValidatorServiceState|)
   (:SRL-namespace |http://sadl.org/Validator.sadl|)
   (:SRL-classname |AutomationRequestValidatorServiceState|)
   (:Interface-definition? nil)
   (:SRL-property-name ())))

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

(defdata |translator_generated_name^http://www.w3.org/2001/XMLSchema#int| (range integer (*SRL-data-minimum* <= _ <= *SRL-data-maximum*)))
(SRL-meta-data
  data-definition
  ((:name |translator_generated_name^http://www.w3.org/2001/XMLSchema#int|)
   (:display-name |int|)
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


(defdecomposition |http://sadl.org/ValidatorReq.sreq_DecompVar0|
()
((|http://sadl.org/Validator.sadl#uxas__messages__task__TaskAutomationRequest| |translator_generated_name^http://sadl.org/Validator.sadl#uxas__messages__task__TaskAutomationRequestP|)))

(deflistrequirement |AutomationRequestReceived_instance_1|
  (    (|http://sadl.org/Validator.sadl#uxas__messages__task__TaskAutomationRequest__Subscription^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| |translator_generated_name^http://sadl.org/Validator.sadl#uxas__messages__task__TaskAutomationRequestP|)
       (|previous(http://sadl.org/Validator.sadl#automationRequestList^http://sadl.org/Validator.sadl#AutomationRequestValidatorService)| |translator_generated_name^LIST_OF_1_TO_1_http://sadl.org/Validator.sadl#uxas__messages__task__TaskAutomationRequestP|)
       (|http://sadl.org/Validator.sadl#maxListLength^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| |translator_generated_name^http://www.w3.org/2001/XMLSchema#int_0_TO_20P|)
       (|http://sadl.org/Validator.sadl#denialOfService^http://sadl.org/Validator.sadl#System| |translator_generated_name^http://www.w3.org/2001/XMLSchema#booleanP|)  )
  (    (|http://sadl.org/Validator.sadl#automationRequestList^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| |translator_generated_name^LIST_OF_1_TO_1_http://sadl.org/Validator.sadl#uxas__messages__task__TaskAutomationRequestP|)  )
(rimplies (and (equal |http://sadl.org/Validator.sadl#uxas__messages__task__TaskAutomationRequest__Subscription^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| (|http://sadl.org/ValidatorReq.sreq_DecompVar0|)) (and (srl-< (len-c  |previous(http://sadl.org/Validator.sadl#automationRequestList^http://sadl.org/Validator.sadl#AutomationRequestValidatorService)|) |http://sadl.org/Validator.sadl#maxListLength^http://sadl.org/Validator.sadl#AutomationRequestValidatorService|) (equal |http://sadl.org/Validator.sadl#denialOfService^http://sadl.org/Validator.sadl#System| 'false))) (equal |http://sadl.org/Validator.sadl#automationRequestList^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| (snoc |http://sadl.org/Validator.sadl#uxas__messages__task__TaskAutomationRequest__Subscription^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| |previous(http://sadl.org/Validator.sadl#automationRequestList^http://sadl.org/Validator.sadl#AutomationRequestValidatorService)|))))

(SRL-meta-data 
  requirement-history 
  ((:SRL-name |AutomationRequestReceived|)
   (:Context 1)
   (:transformations ((grounding AutomationRequestReceived_instance_1)))
   (:RA-name |AutomationRequestReceived_instance_1|)
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
                (:name |previous(http://sadl.org/Validator.sadl#automationRequestList^http://sadl.org/Validator.sadl#AutomationRequestValidatorService)|)
                (:display-name |previous automationRequestList of AutomationRequestValidatorService|)
                (:SRL-names (|previous automationRequestList of AutomationRequestValidatorService|))
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
                  )
                  (
                (:name |http://sadl.org/Validator.sadl#automationRequestList^http://sadl.org/Validator.sadl#AutomationRequestValidatorService|)
                (:display-name |automationRequestList of AutomationRequestValidatorService|)
                (:SRL-names (|automationRequestList of AutomationRequestValidatorService|))
                (:direction controlled)
                (:type list)
                (:min-length 1)
                (:max-length 1)
                (:event-variable? nil)
                )))
  )
)

(deflistrequirement |ResponseReceived_instance_11|
  (    (|previous(http://sadl.org/Validator.sadl#state^http://sadl.org/Validator.sadl#AutomationRequestValidatorService)| |translator_generated_name^http://sadl.org/Validator.sadl#AutomationRequestValidatorServiceStateP|)
       (|previous(http://sadl.org/Validator.sadl#timeSinceLastTimerUpdate^http://sadl.org/Validator.sadl#AutomationRequestValidatorService)| |translator_generated_name^http://www.w3.org/2001/XMLSchema#intP|)
       (|http://sadl.org/Validator.sadl#uxas__messages__task__UniqueAutomationResponse__Subscription^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| |translator_generated_name^http://sadl.org/Validator.sadl#uxas__messages__task__UniqueAutomationResponseP|)
       (|previous(http://sadl.org/Validator.sadl#automationRequestList^http://sadl.org/Validator.sadl#AutomationRequestValidatorService)| |translator_generated_name^LIST_OF_1_TO_1_http://sadl.org/Validator.sadl#uxas__messages__task__TaskAutomationRequestP|)  )
  (    (|http://sadl.org/Validator.sadl#automationRequestList^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| |translator_generated_name^LIST_OF_1_TO_1_http://sadl.org/Validator.sadl#uxas__messages__task__TaskAutomationRequestP|)  )
(rimplies (and (equal |previous(http://sadl.org/Validator.sadl#state^http://sadl.org/Validator.sadl#AutomationRequestValidatorService)| '|http://sadl.org/Validator.sadl#Busy|) (and (srl-<= |previous(http://sadl.org/Validator.sadl#timeSinceLastTimerUpdate^http://sadl.org/Validator.sadl#AutomationRequestValidatorService)| 10) (equal |http://sadl.org/Validator.sadl#uxas__messages__task__UniqueAutomationResponse__Subscription^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| '|http://sadl.org/Validator.sadl#uxas__messages__task__UniqueAutomationResponse|))) (equal |http://sadl.org/Validator.sadl#automationRequestList^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| (remove-nth 1 |previous(http://sadl.org/Validator.sadl#automationRequestList^http://sadl.org/Validator.sadl#AutomationRequestValidatorService)|))))

(SRL-meta-data 
  requirement-history 
  ((:SRL-name |ResponseReceived|)
   (:Context 1)
   (:transformations ((grounding ResponseReceived_instance_11)))
   (:RA-name |ResponseReceived_instance_11|)
   (:ModelGenFile "")
   (:VarMapFile "")
      (:Variables ((
                  (:name |previous(http://sadl.org/Validator.sadl#state^http://sadl.org/Validator.sadl#AutomationRequestValidatorService)|)
                  (:display-name |previous state of AutomationRequestValidatorService|)
                  (:SRL-names (|previous state of AutomationRequestValidatorService|))
                  (:direction monitored)
                  (:type enum)
                  (:event-variable? nil)
                  (:no-contingency-checking? nil)
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
                (:name |previous(http://sadl.org/Validator.sadl#automationRequestList^http://sadl.org/Validator.sadl#AutomationRequestValidatorService)|)
                (:display-name |previous automationRequestList of AutomationRequestValidatorService|)
                (:SRL-names (|previous automationRequestList of AutomationRequestValidatorService|))
                (:direction monitored)
                (:type list)
                (:min-length 1)
                (:max-length 1)
                (:event-variable? nil)
                )
                  (
                (:name |http://sadl.org/Validator.sadl#automationRequestList^http://sadl.org/Validator.sadl#AutomationRequestValidatorService|)
                (:display-name |automationRequestList of AutomationRequestValidatorService|)
                (:SRL-names (|automationRequestList of AutomationRequestValidatorService|))
                (:direction controlled)
                (:type list)
                (:min-length 1)
                (:max-length 1)
                (:event-variable? nil)
                )))
  )
)

(deflistrequirement |Timeout_instance_20|
  (    (|previous(http://sadl.org/Validator.sadl#state^http://sadl.org/Validator.sadl#AutomationRequestValidatorService)| |translator_generated_name^http://sadl.org/Validator.sadl#AutomationRequestValidatorServiceStateP|)
       (|previous(http://sadl.org/Validator.sadl#timeSinceLastTimerUpdate^http://sadl.org/Validator.sadl#AutomationRequestValidatorService)| |translator_generated_name^http://www.w3.org/2001/XMLSchema#intP|)
       (|previous(http://sadl.org/Validator.sadl#automationRequestList^http://sadl.org/Validator.sadl#AutomationRequestValidatorService)| |translator_generated_name^LIST_OF_1_TO_1_http://sadl.org/Validator.sadl#uxas__messages__task__TaskAutomationRequestP|)  )
  (    (|http://sadl.org/Validator.sadl#automationRequestList^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| |translator_generated_name^LIST_OF_1_TO_1_http://sadl.org/Validator.sadl#uxas__messages__task__TaskAutomationRequestP|)  )
(rimplies (and (equal |previous(http://sadl.org/Validator.sadl#state^http://sadl.org/Validator.sadl#AutomationRequestValidatorService)| '|http://sadl.org/Validator.sadl#Busy|) (srl->= |previous(http://sadl.org/Validator.sadl#timeSinceLastTimerUpdate^http://sadl.org/Validator.sadl#AutomationRequestValidatorService)| 10)) (equal |http://sadl.org/Validator.sadl#automationRequestList^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| (remove-nth 1 |previous(http://sadl.org/Validator.sadl#automationRequestList^http://sadl.org/Validator.sadl#AutomationRequestValidatorService)|))))

(SRL-meta-data 
  requirement-history 
  ((:SRL-name |Timeout|)
   (:Context 1)
   (:transformations ((grounding Timeout_instance_19)(normalization body Timeout_instance_19)))
   (:RA-name |Timeout_instance_20|)
   (:ModelGenFile "")
   (:VarMapFile "")
      (:Variables ((
                  (:name |previous(http://sadl.org/Validator.sadl#state^http://sadl.org/Validator.sadl#AutomationRequestValidatorService)|)
                  (:display-name |previous state of AutomationRequestValidatorService|)
                  (:SRL-names (|previous state of AutomationRequestValidatorService|))
                  (:direction monitored)
                  (:type enum)
                  (:event-variable? nil)
                  (:no-contingency-checking? nil)
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
                (:name |previous(http://sadl.org/Validator.sadl#automationRequestList^http://sadl.org/Validator.sadl#AutomationRequestValidatorService)|)
                (:display-name |previous automationRequestList of AutomationRequestValidatorService|)
                (:SRL-names (|previous automationRequestList of AutomationRequestValidatorService|))
                (:direction monitored)
                (:type list)
                (:min-length 1)
                (:max-length 1)
                (:event-variable? nil)
                )
                  (
                (:name |http://sadl.org/Validator.sadl#automationRequestList^http://sadl.org/Validator.sadl#AutomationRequestValidatorService|)
                (:display-name |automationRequestList of AutomationRequestValidatorService|)
                (:SRL-names (|automationRequestList of AutomationRequestValidatorService|))
                (:direction controlled)
                (:type list)
                (:min-length 1)
                (:max-length 1)
                (:event-variable? nil)
                )))
  )
)

(deflistrequirement |Timeout_instance_21|
  (    (|http://sadl.org/Validator.sadl#uxas__messages__task__UniqueAutomationResponse__Subscription^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| |translator_generated_name^http://sadl.org/Validator.sadl#uxas__messages__task__UniqueAutomationResponseP|)
       (|previous(http://sadl.org/Validator.sadl#state^http://sadl.org/Validator.sadl#AutomationRequestValidatorService)| |translator_generated_name^http://sadl.org/Validator.sadl#AutomationRequestValidatorServiceStateP|)
       (|previous(http://sadl.org/Validator.sadl#automationRequestList^http://sadl.org/Validator.sadl#AutomationRequestValidatorService)| |translator_generated_name^LIST_OF_1_TO_1_http://sadl.org/Validator.sadl#uxas__messages__task__TaskAutomationRequestP|)  )
  (    (|http://sadl.org/Validator.sadl#automationRequestList^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| |translator_generated_name^LIST_OF_1_TO_1_http://sadl.org/Validator.sadl#uxas__messages__task__TaskAutomationRequestP|)  )
(rimplies (and (not (equal |http://sadl.org/Validator.sadl#uxas__messages__task__UniqueAutomationResponse__Subscription^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| '|http://sadl.org/Validator.sadl#uxas__messages__task__UniqueAutomationResponse|)) (equal |previous(http://sadl.org/Validator.sadl#state^http://sadl.org/Validator.sadl#AutomationRequestValidatorService)| '|http://sadl.org/Validator.sadl#Busy|)) (equal |http://sadl.org/Validator.sadl#automationRequestList^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| (remove-nth 1 |previous(http://sadl.org/Validator.sadl#automationRequestList^http://sadl.org/Validator.sadl#AutomationRequestValidatorService)|))))

(SRL-meta-data 
  requirement-history 
  ((:SRL-name |Timeout|)
   (:Context 1)
   (:transformations ((grounding Timeout_instance_19)(normalization body Timeout_instance_19)))
   (:RA-name |Timeout_instance_21|)
   (:ModelGenFile "")
   (:VarMapFile "")
      (:Variables ((
                  (:name |http://sadl.org/Validator.sadl#uxas__messages__task__UniqueAutomationResponse__Subscription^http://sadl.org/Validator.sadl#AutomationRequestValidatorService|)
                  (:display-name |uxas__messages__task__UniqueAutomationResponse__Subscription of AutomationRequestValidatorService|)
                  (:SRL-names (|uxas__messages__task__UniqueAutomationResponse__Subscription of AutomationRequestValidatorService|))
                  (:direction monitored)
                  (:type enum)
                  (:event-variable? nil)
                  (:no-contingency-checking? t)
                  )
                  (
                  (:name |previous(http://sadl.org/Validator.sadl#state^http://sadl.org/Validator.sadl#AutomationRequestValidatorService)|)
                  (:display-name |previous state of AutomationRequestValidatorService|)
                  (:SRL-names (|previous state of AutomationRequestValidatorService|))
                  (:direction monitored)
                  (:type enum)
                  (:event-variable? nil)
                  (:no-contingency-checking? nil)
                  )
                  (
                (:name |previous(http://sadl.org/Validator.sadl#automationRequestList^http://sadl.org/Validator.sadl#AutomationRequestValidatorService)|)
                (:display-name |previous automationRequestList of AutomationRequestValidatorService|)
                (:SRL-names (|previous automationRequestList of AutomationRequestValidatorService|))
                (:direction monitored)
                (:type list)
                (:min-length 1)
                (:max-length 1)
                (:event-variable? nil)
                )
                  (
                (:name |http://sadl.org/Validator.sadl#automationRequestList^http://sadl.org/Validator.sadl#AutomationRequestValidatorService|)
                (:display-name |automationRequestList of AutomationRequestValidatorService|)
                (:SRL-names (|automationRequestList of AutomationRequestValidatorService|))
                (:direction controlled)
                (:type list)
                (:min-length 1)
                (:max-length 1)
                (:event-variable? nil)
                )))
  )
)


(defimmaterial |A6_instance_39|
  (    (|previous(http://sadl.org/Validator.sadl#automationRequestList^http://sadl.org/Validator.sadl#AutomationRequestValidatorService)| |translator_generated_name^LIST_OF_1_TO_1_http://sadl.org/Validator.sadl#uxas__messages__task__TaskAutomationRequestP|)
       (|previous(http://sadl.org/Validator.sadl#state^http://sadl.org/Validator.sadl#AutomationRequestValidatorService)| |translator_generated_name^http://sadl.org/Validator.sadl#AutomationRequestValidatorServiceStateP|)  )
  (    (|http://sadl.org/Validator.sadl#automationRequestList^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| |translator_generated_name^LIST_OF_1_TO_1_http://sadl.org/Validator.sadl#uxas__messages__task__TaskAutomationRequestP|)  )
(or (equal (len-c  |previous(http://sadl.org/Validator.sadl#automationRequestList^http://sadl.org/Validator.sadl#AutomationRequestValidatorService)|) 0) (equal |previous(http://sadl.org/Validator.sadl#state^http://sadl.org/Validator.sadl#AutomationRequestValidatorService)| '|http://sadl.org/Validator.sadl#Idle|)))

(SRL-meta-data 
  immaterial-history
  ((:SRL-name |A6|)
   (:context 1)
   (:transformations ((grounding A6_instance_39)))
   (:Assertion-name |A6_instance_39|)
      (:Variables ((
                (:name |http://sadl.org/Validator.sadl#automationRequestList^http://sadl.org/Validator.sadl#AutomationRequestValidatorService|)
                (:display-name |automationRequestList of AutomationRequestValidatorService|)
                (:SRL-names (|automationRequestList of AutomationRequestValidatorService|))
                (:direction controlled)
                (:type list)
                (:min-length 1)
                (:max-length 1)
                (:event-variable? nil)
                )
                  (
                (:name |previous(http://sadl.org/Validator.sadl#automationRequestList^http://sadl.org/Validator.sadl#AutomationRequestValidatorService)|)
                (:display-name |previous automationRequestList of AutomationRequestValidatorService|)
                (:SRL-names (|previous automationRequestList of AutomationRequestValidatorService|))
                (:direction monitored)
                (:type list)
                (:min-length 1)
                (:max-length 1)
                (:event-variable? nil)
                )
                  (
                  (:name |previous(http://sadl.org/Validator.sadl#state^http://sadl.org/Validator.sadl#AutomationRequestValidatorService)|)
                  (:display-name |previous state of AutomationRequestValidatorService|)
                  (:SRL-names (|previous state of AutomationRequestValidatorService|))
                  (:direction monitored)
                  (:type enum)
                  (:event-variable? nil)
                  (:no-contingency-checking? nil)
                  )))
  )
)

(defimmaterial |A5_instance_38|
  (    (|previous(http://sadl.org/Validator.sadl#automationRequestList^http://sadl.org/Validator.sadl#AutomationRequestValidatorService)| |translator_generated_name^LIST_OF_1_TO_1_http://sadl.org/Validator.sadl#uxas__messages__task__TaskAutomationRequestP|)
       (|http://sadl.org/Validator.sadl#maxListLength^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| |translator_generated_name^http://www.w3.org/2001/XMLSchema#int_0_TO_20P|)
       (|previous(http://sadl.org/Validator.sadl#state^http://sadl.org/Validator.sadl#AutomationRequestValidatorService)| |translator_generated_name^http://sadl.org/Validator.sadl#AutomationRequestValidatorServiceStateP|)  )
  (    (|http://sadl.org/Validator.sadl#automationRequestList^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| |translator_generated_name^LIST_OF_1_TO_1_http://sadl.org/Validator.sadl#uxas__messages__task__TaskAutomationRequestP|)  )
(or (srl->= (len-c  |previous(http://sadl.org/Validator.sadl#automationRequestList^http://sadl.org/Validator.sadl#AutomationRequestValidatorService)|) |http://sadl.org/Validator.sadl#maxListLength^http://sadl.org/Validator.sadl#AutomationRequestValidatorService|) (equal |previous(http://sadl.org/Validator.sadl#state^http://sadl.org/Validator.sadl#AutomationRequestValidatorService)| '|http://sadl.org/Validator.sadl#Idle|)))

(SRL-meta-data 
  immaterial-history
  ((:SRL-name |A5|)
   (:context 1)
   (:transformations ((grounding A5_instance_38)))
   (:Assertion-name |A5_instance_38|)
      (:Variables ((
                (:name |http://sadl.org/Validator.sadl#automationRequestList^http://sadl.org/Validator.sadl#AutomationRequestValidatorService|)
                (:display-name |automationRequestList of AutomationRequestValidatorService|)
                (:SRL-names (|automationRequestList of AutomationRequestValidatorService|))
                (:direction controlled)
                (:type list)
                (:min-length 1)
                (:max-length 1)
                (:event-variable? nil)
                )
                  (
                (:name |previous(http://sadl.org/Validator.sadl#automationRequestList^http://sadl.org/Validator.sadl#AutomationRequestValidatorService)|)
                (:display-name |previous automationRequestList of AutomationRequestValidatorService|)
                (:SRL-names (|previous automationRequestList of AutomationRequestValidatorService|))
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
                  (:name |previous(http://sadl.org/Validator.sadl#state^http://sadl.org/Validator.sadl#AutomationRequestValidatorService)|)
                  (:display-name |previous state of AutomationRequestValidatorService|)
                  (:SRL-names (|previous state of AutomationRequestValidatorService|))
                  (:direction monitored)
                  (:type enum)
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
  ((:name |Validator.sadl_uxas__messages__task__UniqueAutomationResponse_Val_1|)
   (:display-name |Validator.sadl_uxas__messages__task__UniqueAutomationResponse_Val_1|)
   (:SRL-name |Validator.sadl_uxas__messages__task__UniqueAutomationResponse_Val_1|)))


(SRL-meta-data 
  no-contingency-checking-register
  ((:name |translator_generated_name^http://sadl.org/Validator.sadl#uxas__messages__task__UniqueAutomationResponse|)))


(SRL-meta-data 
  context 
  ((:context-id 1)
   (:exp (|true|))))

