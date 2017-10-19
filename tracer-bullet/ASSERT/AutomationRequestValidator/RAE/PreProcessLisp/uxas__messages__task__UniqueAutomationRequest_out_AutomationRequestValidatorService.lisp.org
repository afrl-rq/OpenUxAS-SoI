; Generated using ACL2s Translator Version 3.0.0.201709292107_java 
; and RCE SADL Feature 2.1.0.201709221328
(in-package "ACL2S")
(set-ignore-ok t)
(defttag :progn!)
(include-book "requirements-analyses-book")

(defdata |translator_generated_name^http://www.w3.org/2001/XMLSchema#int| (range integer (*SRL-data-minimum* <= _ <= *SRL-data-maximum*)))
(SRL-meta-data
  data-definition
  ((:name |translator_generated_name^http://www.w3.org/2001/XMLSchema#int|)
   (:display-name |int|)
   (:SRL-namespace |http://www.w3.org/2001/XMLSchema|)
   (:SRL-classname |int|)
   (:Interface-definition? nil)
   (:SRL-property-name ())))

(defdata |translator_generated_name^http://sadl.org/Validator.sadl#uxas__messages__task__UniqueAutomationRequest| (enum '(|Validator.sadl_uxas__messages__task__UniqueAutomationRequest_Val_1| )))
(SRL-meta-data
  data-definition
  ((:name |translator_generated_name^http://sadl.org/Validator.sadl#uxas__messages__task__UniqueAutomationRequest|)
   (:display-name |uxas__messages__task__UniqueAutomationRequest|)
   (:SRL-namespace |http://sadl.org/Validator.sadl|)
   (:SRL-classname |uxas__messages__task__UniqueAutomationRequest|)
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

(defdecomposition |http://sadl.org/Validator.sadl#result^http://sadl.org/ValidatorReq.sreq#newid_PublishAutomationRequest|
()
((|http://sadl.org/Validator.sadl#result^http://sadl.org/Validator.sadl#GenID| |translator_generated_name^http://www.w3.org/2001/XMLSchema#intP|)))
(defdecomposition |http://sadl.org/ValidatorReq.sreq#msg_PublishAutomationRequest|
((|http://sadl.org/Validator.sadl#ResponseID^http://sadl.org/Validator.sadl#uxas__messages__task__UniqueAutomationRequest| |translator_generated_name^http://www.w3.org/2001/XMLSchema#intP|))
((|http://sadl.org/Validator.sadl#uxas__messages__task__UniqueAutomationRequest| |translator_generated_name^http://sadl.org/Validator.sadl#uxas__messages__task__UniqueAutomationRequestP|)))

(deflistrequirement |PublishAutomationRequest_instance_29|
  (    (|previous(http://sadl.org/Validator.sadl#state^http://sadl.org/Validator.sadl#AutomationRequestValidatorService)| |translator_generated_name^http://sadl.org/Validator.sadl#AutomationRequestValidatorServiceStateP|)
       (|http://sadl.org/Validator.sadl#automationRequestList^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| |translator_generated_name^LIST_OF_1_TO_1_http://sadl.org/Validator.sadl#uxas__messages__task__TaskAutomationRequestP|)  )
  (    (|http://sadl.org/Validator.sadl#uxas__messages__task__UniqueAutomationRequest_out^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| |translator_generated_name^http://sadl.org/Validator.sadl#uxas__messages__task__UniqueAutomationRequestP|)  )
(rimplies (and (equal |previous(http://sadl.org/Validator.sadl#state^http://sadl.org/Validator.sadl#AutomationRequestValidatorService)| '|http://sadl.org/Validator.sadl#Idle|) (srl-> (len-c  |http://sadl.org/Validator.sadl#automationRequestList^http://sadl.org/Validator.sadl#AutomationRequestValidatorService|) 0)) (equal |http://sadl.org/Validator.sadl#uxas__messages__task__UniqueAutomationRequest_out^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| (|http://sadl.org/ValidatorReq.sreq#msg_PublishAutomationRequest| (|http://sadl.org/Validator.sadl#result^http://sadl.org/ValidatorReq.sreq#newid_PublishAutomationRequest|)))))

(SRL-meta-data 
  requirement-history 
  ((:SRL-name |PublishAutomationRequest|)
   (:Context 1)
   (:transformations ((grounding PublishAutomationRequest_instance_29)))
   (:RA-name |PublishAutomationRequest_instance_29|)
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
                  (:name |http://sadl.org/Validator.sadl#uxas__messages__task__UniqueAutomationRequest_out^http://sadl.org/Validator.sadl#AutomationRequestValidatorService|)
                  (:display-name |uxas__messages__task__UniqueAutomationRequest_out of AutomationRequestValidatorService|)
                  (:SRL-names (|uxas__messages__task__UniqueAutomationRequest_out of AutomationRequestValidatorService|))
                  (:direction controlled)
                  (:type enum)
                  (:event-variable? nil)
                  (:no-contingency-checking? nil)
                  )))
  )
)


(defimmaterial |A2_instance_35|
  (    (|previous(http://sadl.org/Validator.sadl#state^http://sadl.org/Validator.sadl#AutomationRequestValidatorService)| |translator_generated_name^http://sadl.org/Validator.sadl#AutomationRequestValidatorServiceStateP|)
       (|http://sadl.org/Validator.sadl#automationRequestList^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| |translator_generated_name^LIST_OF_1_TO_1_http://sadl.org/Validator.sadl#uxas__messages__task__TaskAutomationRequestP|)  )
  (    (|http://sadl.org/Validator.sadl#uxas__messages__task__UniqueAutomationRequest_out^http://sadl.org/Validator.sadl#AutomationRequestValidatorService| |translator_generated_name^http://sadl.org/Validator.sadl#uxas__messages__task__UniqueAutomationRequestP|)  )
(not (and (equal |previous(http://sadl.org/Validator.sadl#state^http://sadl.org/Validator.sadl#AutomationRequestValidatorService)| '|http://sadl.org/Validator.sadl#Idle|) (srl-> (len-c  |http://sadl.org/Validator.sadl#automationRequestList^http://sadl.org/Validator.sadl#AutomationRequestValidatorService|) 0))))

(SRL-meta-data 
  immaterial-history
  ((:SRL-name |A2|)
   (:context 1)
   (:transformations ((grounding A2_instance_35)))
   (:Assertion-name |A2_instance_35|)
      (:Variables ((
                  (:name |http://sadl.org/Validator.sadl#uxas__messages__task__UniqueAutomationRequest_out^http://sadl.org/Validator.sadl#AutomationRequestValidatorService|)
                  (:display-name |uxas__messages__task__UniqueAutomationRequest_out of AutomationRequestValidatorService|)
                  (:SRL-names (|uxas__messages__task__UniqueAutomationRequest_out of AutomationRequestValidatorService|))
                  (:direction controlled)
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
                (:name |http://sadl.org/Validator.sadl#automationRequestList^http://sadl.org/Validator.sadl#AutomationRequestValidatorService|)
                (:display-name |automationRequestList of AutomationRequestValidatorService|)
                (:SRL-names (|automationRequestList of AutomationRequestValidatorService|))
                (:direction monitored)
                (:type list)
                (:min-length 1)
                (:max-length 1)
                (:event-variable? nil)
                )))
  )
)



(SRL-meta-data 
  constant
  ((:name |Validator.sadl_uxas__messages__task__UniqueAutomationRequest_Val_1|)
   (:display-name |Validator.sadl_uxas__messages__task__UniqueAutomationRequest_Val_1|)
   (:SRL-name |Validator.sadl_uxas__messages__task__UniqueAutomationRequest_Val_1|)))

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
  context 
  ((:context-id 1)
   (:exp (|true|))))


(SRL-meta-data 
	decomposition-history
	((:RA-requirement |PublishAutomationRequest_instance_28|)
	 (:Decomp-var |http://sadl.org/Validator.sadl#result^http://sadl.org/ValidatorReq.sreq#newid_PublishAutomationRequest|)
	 (:Type :linked)
	 (:Decomp-def |result of GenID|)
	 (:SRL-name |result of newid|)
	 (:RA-decomp-requirements ())
	 (:Var-correspondence (
		)))
)


(SRL-meta-data 
	decomposition-history
	((:RA-requirement |PublishAutomationRequest_instance_28|)
	 (:Decomp-var |http://sadl.org/ValidatorReq.sreq#msg_PublishAutomationRequest|)
	 (:Type :linked)
	 (:Decomp-def |uxas__messages__task__UniqueAutomationRequest|)
	 (:SRL-name |msg|)
	 (:RA-decomp-requirements ())
	 (:Var-correspondence (
		(|http://sadl.org/Validator.sadl#result^http://sadl.org/ValidatorReq.sreq#newid_PublishAutomationRequest| |http://sadl.org/Validator.sadl#ResponseID^http://sadl.org/Validator.sadl#uxas__messages__task__UniqueAutomationRequest|))))
)

