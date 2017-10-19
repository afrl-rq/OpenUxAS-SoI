; Generated using ACL2s Translator Version 3.0.0.201709292107_java 
; and RCE SADL Feature 2.1.0.201709221328
(in-package "ACL2S")
(set-ignore-ok t)
(defttag :progn!)
(include-book "requirements-analyses-book")

(defdata |translator_generated_name^http://sadl.org/Validator.sadl#AutomationRequestValidatorServiceState| (enum '(|http://sadl.org/Validator.sadl#Idle| |http://sadl.org/Validator.sadl#Busy| )))
(SRL-meta-data
  data-definition
  ((:name |translator_generated_name^http://sadl.org/Validator.sadl#AutomationRequestValidatorServiceState|)
   (:display-name |AutomationRequestValidatorServiceState|)
   (:SRL-namespace |http://sadl.org/Validator.sadl|)
   (:SRL-classname |AutomationRequestValidatorServiceState|)
   (:Interface-definition? nil)
   (:SRL-property-name ())))

(defdata |translator_generated_name^http://sadl.org/Validator.sadl#uxas__messages__task__TaskAutomationRequest| (enum '(|Validator.sadl_uxas__messages__task__TaskAutomationRequest_Val| )))
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


(deflistrequirement |PublishAutomationRequest_instance_31|
  (    (|previous(http://sadl.org/Validator.sadl#state^http://sadl.org/Validator.sadl#AutomationRequestValidatorService)| |translator_generated_name^http://sadl.org/Validator.sadl#AutomationRequestValidatorServiceStateP|)
       (|http://sadl.org/Validator.sadl#automationRequestList^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| |translator_generated_name^LIST_OF_1_TO_1_http://sadl.org/Validator.sadl#uxas__messages__task__TaskAutomationRequestP|)  )
  (    (|http://sadl.org/Validator.sadl#state^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| |translator_generated_name^http://sadl.org/Validator.sadl#AutomationRequestValidatorServiceStateP|)  )
(rimplies (and (equal |previous(http://sadl.org/Validator.sadl#state^http://sadl.org/Validator.sadl#AutomationRequestValidatorService)| '|http://sadl.org/Validator.sadl#Idle|) (srl-> (len-c  |http://sadl.org/Validator.sadl#automationRequestList^http://sadl.org/Validator.sadl#AutomationRequestValidatorService|) 0)) (equal |http://sadl.org/Validator.sadl#state^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| '|http://sadl.org/Validator.sadl#Busy|)))

(SRL-meta-data 
  requirement-history 
  ((:SRL-name |PublishAutomationRequest|)
   (:Context 1)
   (:transformations ((grounding PublishAutomationRequest_instance_31)))
   (:RA-name |PublishAutomationRequest_instance_31|)
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
                  (:name |http://sadl.org/Validator.sadl#state^http://sadl.org/Validator.sadl#AutomationRequestValidatorService|)
                  (:display-name |state of AutomationRequestValidatorService|)
                  (:SRL-names (|state of AutomationRequestValidatorService|))
                  (:direction controlled)
                  (:type enum)
                  (:event-variable? nil)
                  (:no-contingency-checking? t)
                  )))
  )
)

(deflistrequirement |PublishAutomationRequest2_instance_33|
  (    (|previous(http://sadl.org/Validator.sadl#state^http://sadl.org/Validator.sadl#AutomationRequestValidatorService)| |translator_generated_name^http://sadl.org/Validator.sadl#AutomationRequestValidatorServiceStateP|)
       (|http://sadl.org/Validator.sadl#automationRequestList^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| |translator_generated_name^LIST_OF_1_TO_1_http://sadl.org/Validator.sadl#uxas__messages__task__TaskAutomationRequestP|)  )
  (    (|http://sadl.org/Validator.sadl#state^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| |translator_generated_name^http://sadl.org/Validator.sadl#AutomationRequestValidatorServiceStateP|)  )
(rimplies (and (equal |previous(http://sadl.org/Validator.sadl#state^http://sadl.org/Validator.sadl#AutomationRequestValidatorService)| '|http://sadl.org/Validator.sadl#Idle|) (equal (len-c  |http://sadl.org/Validator.sadl#automationRequestList^http://sadl.org/Validator.sadl#AutomationRequestValidatorService|) 0)) (equal |http://sadl.org/Validator.sadl#state^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| '|http://sadl.org/Validator.sadl#Idle|)))

(SRL-meta-data 
  requirement-history 
  ((:SRL-name |PublishAutomationRequest2|)
   (:Context 1)
   (:transformations ((grounding PublishAutomationRequest2_instance_33)))
   (:RA-name |PublishAutomationRequest2_instance_33|)
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
                  (:name |http://sadl.org/Validator.sadl#state^http://sadl.org/Validator.sadl#AutomationRequestValidatorService|)
                  (:display-name |state of AutomationRequestValidatorService|)
                  (:SRL-names (|state of AutomationRequestValidatorService|))
                  (:direction controlled)
                  (:type enum)
                  (:event-variable? nil)
                  (:no-contingency-checking? t)
                  )))
  )
)

(defrequirement |ResponseReceived_instance_15|
  (    (|previous(http://sadl.org/Validator.sadl#state^http://sadl.org/Validator.sadl#AutomationRequestValidatorService)| |translator_generated_name^http://sadl.org/Validator.sadl#AutomationRequestValidatorServiceStateP|)
       (|previous(http://sadl.org/Validator.sadl#timeSinceLastTimerUpdate^http://sadl.org/Validator.sadl#AutomationRequestValidatorService)| |translator_generated_name^http://www.w3.org/2001/XMLSchema#intP|)
       (|http://sadl.org/Validator.sadl#uxas__messages__task__UniqueAutomationResponse__Subscription^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| |translator_generated_name^http://sadl.org/Validator.sadl#uxas__messages__task__UniqueAutomationResponseP|)  )
  (    (|http://sadl.org/Validator.sadl#state^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| |translator_generated_name^http://sadl.org/Validator.sadl#AutomationRequestValidatorServiceStateP|)  )
(rimplies (and (and (equal |previous(http://sadl.org/Validator.sadl#state^http://sadl.org/Validator.sadl#AutomationRequestValidatorService)| '|http://sadl.org/Validator.sadl#Busy|) (srl-<= |previous(http://sadl.org/Validator.sadl#timeSinceLastTimerUpdate^http://sadl.org/Validator.sadl#AutomationRequestValidatorService)| 10)) (equal |http://sadl.org/Validator.sadl#uxas__messages__task__UniqueAutomationResponse__Subscription^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| '|http://sadl.org/Validator.sadl#uxas__messages__task__UniqueAutomationResponse|)) (equal |http://sadl.org/Validator.sadl#state^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| '|http://sadl.org/Validator.sadl#Idle|)))

(SRL-meta-data 
  requirement-history 
  ((:SRL-name |ResponseReceived|)
   (:Context 1)
   (:transformations ((grounding ResponseReceived_instance_15)))
   (:RA-name |ResponseReceived_instance_15|)
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
                  (:name |http://sadl.org/Validator.sadl#state^http://sadl.org/Validator.sadl#AutomationRequestValidatorService|)
                  (:display-name |state of AutomationRequestValidatorService|)
                  (:SRL-names (|state of AutomationRequestValidatorService|))
                  (:direction controlled)
                  (:type enum)
                  (:event-variable? nil)
                  (:no-contingency-checking? t)
                  )))
  )
)

(defrequirement |Timeout_instance_25|
  (    (|previous(http://sadl.org/Validator.sadl#state^http://sadl.org/Validator.sadl#AutomationRequestValidatorService)| |translator_generated_name^http://sadl.org/Validator.sadl#AutomationRequestValidatorServiceStateP|)
       (|previous(http://sadl.org/Validator.sadl#timeSinceLastTimerUpdate^http://sadl.org/Validator.sadl#AutomationRequestValidatorService)| |translator_generated_name^http://www.w3.org/2001/XMLSchema#intP|)
       (|http://sadl.org/Validator.sadl#uxas__messages__task__UniqueAutomationResponse__Subscription^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| |translator_generated_name^http://sadl.org/Validator.sadl#uxas__messages__task__UniqueAutomationResponseP|)  )
  (    (|http://sadl.org/Validator.sadl#state^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| |translator_generated_name^http://sadl.org/Validator.sadl#AutomationRequestValidatorServiceStateP|)  )
(rimplies (and (equal |previous(http://sadl.org/Validator.sadl#state^http://sadl.org/Validator.sadl#AutomationRequestValidatorService)| '|http://sadl.org/Validator.sadl#Busy|) (or (srl->= |previous(http://sadl.org/Validator.sadl#timeSinceLastTimerUpdate^http://sadl.org/Validator.sadl#AutomationRequestValidatorService)| 10) (not (equal |http://sadl.org/Validator.sadl#uxas__messages__task__UniqueAutomationResponse__Subscription^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| '|http://sadl.org/Validator.sadl#uxas__messages__task__UniqueAutomationResponse|)))) (equal |http://sadl.org/Validator.sadl#state^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| '|http://sadl.org/Validator.sadl#Idle|)))

(SRL-meta-data 
  requirement-history 
  ((:SRL-name |Timeout|)
   (:Context 1)
   (:transformations ((grounding Timeout_instance_25)))
   (:RA-name |Timeout_instance_25|)
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
                  (:name |http://sadl.org/Validator.sadl#state^http://sadl.org/Validator.sadl#AutomationRequestValidatorService|)
                  (:display-name |state of AutomationRequestValidatorService|)
                  (:SRL-names (|state of AutomationRequestValidatorService|))
                  (:direction controlled)
                  (:type enum)
                  (:event-variable? nil)
                  (:no-contingency-checking? t)
                  )))
  )
)



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
  ((:name |Validator.sadl_uxas__messages__task__TaskAutomationRequest_Val|)
   (:display-name |Validator.sadl_uxas__messages__task__TaskAutomationRequest_Val|)
   (:SRL-name |Validator.sadl_uxas__messages__task__TaskAutomationRequest_Val|)))

(SRL-meta-data 
  constant
  ((:name |Validator.sadl_uxas__messages__task__UniqueAutomationResponse_Val_1|)
   (:display-name |Validator.sadl_uxas__messages__task__UniqueAutomationResponse_Val_1|)
   (:SRL-name |Validator.sadl_uxas__messages__task__UniqueAutomationResponse_Val_1|)))


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

