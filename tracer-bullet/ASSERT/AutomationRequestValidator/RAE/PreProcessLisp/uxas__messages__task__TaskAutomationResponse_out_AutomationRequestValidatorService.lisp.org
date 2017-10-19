; Generated using ACL2s Translator Version 3.0.0.201709292107_java 
; and RCE SADL Feature 2.1.0.201709221328
(in-package "ACL2S")
(set-ignore-ok t)
(defttag :progn!)
(include-book "requirements-analyses-book")

(defdata |translator_generated_name^http://sadl.org/Validator.sadl#uxas__messages__task__TaskAutomationResponse| (enum '(|Validator.sadl_uxas__messages__task__TaskAutomationResponse_Val_1| |Validator.sadl_uxas__messages__task__TaskAutomationResponse_Val_2| )))
(SRL-meta-data
  data-definition
  ((:name |translator_generated_name^http://sadl.org/Validator.sadl#uxas__messages__task__TaskAutomationResponse|)
   (:display-name |uxas__messages__task__TaskAutomationResponse|)
   (:SRL-namespace |http://sadl.org/Validator.sadl|)
   (:SRL-classname |uxas__messages__task__TaskAutomationResponse|)
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

(defdata |translator_generated_name^http://www.w3.org/2001/XMLSchema#int| (range integer (*SRL-data-minimum* <= _ <= *SRL-data-maximum*)))
(SRL-meta-data
  data-definition
  ((:name |translator_generated_name^http://www.w3.org/2001/XMLSchema#int|)
   (:display-name |int|)
   (:SRL-namespace |http://www.w3.org/2001/XMLSchema|)
   (:SRL-classname |int|)
   (:Interface-definition? nil)
   (:SRL-property-name ())))


(defrequirement |ResponseReceived_instance_13|
  (    (|previous(http://sadl.org/Validator.sadl#state^http://sadl.org/Validator.sadl#AutomationRequestValidatorService)| |translator_generated_name^http://sadl.org/Validator.sadl#AutomationRequestValidatorServiceStateP|)
       (|previous(http://sadl.org/Validator.sadl#timeSinceLastTimerUpdate^http://sadl.org/Validator.sadl#AutomationRequestValidatorService)| |translator_generated_name^http://www.w3.org/2001/XMLSchema#intP|)
       (|http://sadl.org/Validator.sadl#uxas__messages__task__UniqueAutomationResponse__Subscription^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| |translator_generated_name^http://sadl.org/Validator.sadl#uxas__messages__task__UniqueAutomationResponseP|)
       (|http://sadl.org/Validator.sadl#content^http://sadl.org/Validator.sadl#uxas__messages__task__UniqueAutomationResponse| |translator_generated_name^http://sadl.org/Validator.sadl#uxas__messages__task__TaskAutomationResponseP|)  )
  (    (|http://sadl.org/Validator.sadl#uxas__messages__task__TaskAutomationResponse_out^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| |translator_generated_name^http://sadl.org/Validator.sadl#uxas__messages__task__TaskAutomationResponseP|)  )
(rimplies (and (and (equal |previous(http://sadl.org/Validator.sadl#state^http://sadl.org/Validator.sadl#AutomationRequestValidatorService)| '|http://sadl.org/Validator.sadl#Busy|) (srl-<= |previous(http://sadl.org/Validator.sadl#timeSinceLastTimerUpdate^http://sadl.org/Validator.sadl#AutomationRequestValidatorService)| 10)) (equal |http://sadl.org/Validator.sadl#uxas__messages__task__UniqueAutomationResponse__Subscription^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| '|http://sadl.org/Validator.sadl#uxas__messages__task__UniqueAutomationResponse|)) (equal |http://sadl.org/Validator.sadl#uxas__messages__task__TaskAutomationResponse_out^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| |http://sadl.org/Validator.sadl#content^http://sadl.org/Validator.sadl#uxas__messages__task__UniqueAutomationResponse|)))

(SRL-meta-data 
  requirement-history 
  ((:SRL-name |ResponseReceived|)
   (:Context 1)
   (:transformations ((grounding ResponseReceived_instance_13)))
   (:RA-name |ResponseReceived_instance_13|)
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
                  (:no-contingency-checking? nil)
                  )
                  (
                  (:name |http://sadl.org/Validator.sadl#content^http://sadl.org/Validator.sadl#uxas__messages__task__UniqueAutomationResponse|)
                  (:display-name |content of uxas__messages__task__UniqueAutomationResponse|)
                  (:SRL-names (|content of uxas__messages__task__UniqueAutomationResponse|))
                  (:direction monitored)
                  (:type enum)
                  (:event-variable? nil)
                  (:no-contingency-checking? t)
                  )
                  (
                  (:name |http://sadl.org/Validator.sadl#uxas__messages__task__TaskAutomationResponse_out^http://sadl.org/Validator.sadl#AutomationRequestValidatorService|)
                  (:display-name |uxas__messages__task__TaskAutomationResponse_out of AutomationRequestValidatorService|)
                  (:SRL-names (|uxas__messages__task__TaskAutomationResponse_out of AutomationRequestValidatorService|))
                  (:direction controlled)
                  (:type enum)
                  (:event-variable? nil)
                  (:no-contingency-checking? t)
                  )))
  )
)


(defimmaterial |A3_instance_36|
  (    (|http://sadl.org/Validator.sadl#uxas__messages__task__UniqueAutomationResponse__Subscription^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| |translator_generated_name^http://sadl.org/Validator.sadl#uxas__messages__task__UniqueAutomationResponseP|)
       (|previous(http://sadl.org/Validator.sadl#state^http://sadl.org/Validator.sadl#AutomationRequestValidatorService)| |translator_generated_name^http://sadl.org/Validator.sadl#AutomationRequestValidatorServiceStateP|)
       (|http://sadl.org/Validator.sadl#timeSinceLastTimerUpdate^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| |translator_generated_name^http://www.w3.org/2001/XMLSchema#int_0_TO_11P|)  )
  (    (|http://sadl.org/Validator.sadl#uxas__messages__task__TaskAutomationResponse_out^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| |translator_generated_name^http://sadl.org/Validator.sadl#uxas__messages__task__TaskAutomationResponseP|)  )
(and (equal |http://sadl.org/Validator.sadl#uxas__messages__task__UniqueAutomationResponse__Subscription^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| (|http://sadl.org/ValidatorReq.sreq_DecompVar2|)) (or (equal |previous(http://sadl.org/Validator.sadl#state^http://sadl.org/Validator.sadl#AutomationRequestValidatorService)| '|http://sadl.org/Validator.sadl#Idle|) (srl->= |http://sadl.org/Validator.sadl#timeSinceLastTimerUpdate^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| 10))))

(SRL-meta-data 
  immaterial-history
  ((:SRL-name |A3|)
   (:context 1)
   (:transformations ((grounding A3_instance_36)))
   (:Assertion-name |A3_instance_36|)
      (:Variables ((
                  (:name |http://sadl.org/Validator.sadl#uxas__messages__task__TaskAutomationResponse_out^http://sadl.org/Validator.sadl#AutomationRequestValidatorService|)
                  (:display-name |uxas__messages__task__TaskAutomationResponse_out of AutomationRequestValidatorService|)
                  (:SRL-names (|uxas__messages__task__TaskAutomationResponse_out of AutomationRequestValidatorService|))
                  (:direction controlled)
                  (:type enum)
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
                  )))
  )
)



(SRL-meta-data 
  constant
  ((:name |Validator.sadl_uxas__messages__task__TaskAutomationResponse_Val_1|)
   (:display-name |Validator.sadl_uxas__messages__task__TaskAutomationResponse_Val_1|)
   (:SRL-name |Validator.sadl_uxas__messages__task__TaskAutomationResponse_Val_1|)))

(SRL-meta-data 
  constant
  ((:name |Validator.sadl_uxas__messages__task__TaskAutomationResponse_Val_2|)
   (:display-name |Validator.sadl_uxas__messages__task__TaskAutomationResponse_Val_2|)
   (:SRL-name |Validator.sadl_uxas__messages__task__TaskAutomationResponse_Val_2|)))

(SRL-meta-data 
  constant
  ((:name |Validator.sadl_uxas__messages__task__UniqueAutomationResponse_Val_1|)
   (:display-name |Validator.sadl_uxas__messages__task__UniqueAutomationResponse_Val_1|)
   (:SRL-name |Validator.sadl_uxas__messages__task__UniqueAutomationResponse_Val_1|)))

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
  no-contingency-checking-register
  ((:name |translator_generated_name^http://sadl.org/Validator.sadl#uxas__messages__task__TaskAutomationResponse|)))


(SRL-meta-data 
  context 
  ((:context-id 1)
   (:exp (|true|))))

