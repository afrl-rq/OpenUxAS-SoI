; RAE Version: 2017-9-16

(IN-PACKAGE "ACL2S")
(DEFTTAG :PROGN!)
(DEFCONST *SRL-DATA-MINIMUM* (- (EXPT 2 31)))
(DEFCONST *SRL-DATA-MAXIMUM* (- (EXPT 2 31) 1))

; Data Definitions
(DEFDATA |int|
 (RANGE INTEGER (*SRL-DATA-MINIMUM* <= _ <= *SRL-DATA-MAXIMUM*)))

(DEFDATA |uxas__messages__task__UniqueAutomationRequest|
 '|Validator.sadl_uxas__messages__task__UniqueAutomationRequest_Val_1|)
(IN-THEORY (DISABLE |uxas__messages__task__UniqueAutomationRequestP|))
(ADD-DEFAULT-HINTS!
 '((STAGE |uxas__messages__task__UniqueAutomationRequestP| 2)))

(DEFDATA |AutomationRequestValidatorServiceState|
 (ONEOF '|Idle| '|Busy|))
(IN-THEORY (DISABLE |AutomationRequestValidatorServiceStateP|))
(ADD-DEFAULT-HINTS!
 '((STAGE |AutomationRequestValidatorServiceStateP| 2)))

(DEFDATA |uxas__messages__task__TaskAutomationRequest|
 '|Validator.sadl_uxas__messages__task__TaskAutomationRequest_Val|)
(IN-THEORY (DISABLE |uxas__messages__task__TaskAutomationRequestP|))
(ADD-DEFAULT-HINTS!
 '((STAGE |uxas__messages__task__TaskAutomationRequestP| 2)))

(DEFDATA
 |LIST_OF_1_TO_1_uxas__messages__task__TaskAutomationRequest-SRL-AUX|
 (LISTOF |uxas__messages__task__TaskAutomationRequest|)
 :MIN-REC-DEPTH 0 :MAX-REC-DEPTH 2)
(DEFUNCR
 |LIST_OF_1_TO_1_uxas__messages__task__TaskAutomationRequestP| (X)
 :INPUT-CONTRACT T :OUTPUT-CONTRACT
 (BOOLEANP
  (|LIST_OF_1_TO_1_uxas__messages__task__TaskAutomationRequestP| X))
 (AND (|LIST_OF_1_TO_1_uxas__messages__task__TaskAutomationRequest-SRL-AUXP|
       X)
      (>= (LEN X) 1)
      (<= (LEN X) 1)))
(DEFTHM
 |LIST_OF_1_TO_1_uxas__messages__task__TaskAutomationRequest-FC-RULE|
 (IMPLIES
  (AND (|LIST_OF_1_TO_1_uxas__messages__task__TaskAutomationRequest-SRL-AUXP|
        X)
       (>= (LEN X) 1)
       (<= (LEN X) 1))
  (|LIST_OF_1_TO_1_uxas__messages__task__TaskAutomationRequestP| X))
 :RULE-CLASSES (:FORWARD-CHAINING))
(DEFTHM
 |LIST_OF_1_TO_1_uxas__messages__task__TaskAutomationRequest-IMPLIES-TLP|
 (IMPLIES
  (|LIST_OF_1_TO_1_uxas__messages__task__TaskAutomationRequestP| X)
  (TRUE-LISTP X))
 :HINTS (("Goal" :IN-THEORY (ENABLE TRUE-LISTP))) :RULE-CLASSES
 ((:FORWARD-CHAINING) (:COMPOUND-RECOGNIZER)
  (:REWRITE :BACKCHAIN-LIMIT-LST 1)))

(DEFTHM |int-INTEGER-THM| (IMPLIES (|intP| X) (INTEGERP X)))
(DEFTHM |int-RATIONAL-THM| (IMPLIES (|intP| X) (RATIONALP X)))

; Decomposition Functions
(DEFSTUB
 |http://sadl.org/Validator.sadl#result^http://sadl.org/ValidatorReq.sreq#newid_PublishAutomationRequest_defstub|
 NIL => *)
(SKIP-PROOFS
 (DEFUNC
  |http://sadl.org/Validator.sadl#result^http://sadl.org/ValidatorReq.sreq#newid_PublishAutomationRequest|
  NIL :INPUT-CONTRACT (AND) :OUTPUT-CONTRACT
  (|intP|
   (|http://sadl.org/Validator.sadl#result^http://sadl.org/ValidatorReq.sreq#newid_PublishAutomationRequest|))
  (|http://sadl.org/Validator.sadl#result^http://sadl.org/ValidatorReq.sreq#newid_PublishAutomationRequest_defstub|)))
(IN-THEORY
 (DISABLE
  |http://sadl.org/Validator.sadl#result^http://sadl.org/ValidatorReq.sreq#newid_PublishAutomationRequest|
  (|http://sadl.org/Validator.sadl#result^http://sadl.org/ValidatorReq.sreq#newid_PublishAutomationRequest|)
  |http://sadl.org/Validator.sadl#result^http://sadl.org/ValidatorReq.sreq#newid_PublishAutomationRequest-DEFINITION-RULE|))

(DEFSTUB
 |http://sadl.org/ValidatorReq.sreq#msg_PublishAutomationRequest_defstub|
 (*) => *)
(SKIP-PROOFS
 (DEFUNC
  |http://sadl.org/ValidatorReq.sreq#msg_PublishAutomationRequest|
  (|http://sadl.org/Validator.sadl#ResponseID^http://sadl.org/Validator.sadl#uxas__messages__task__UniqueAutomationRequest|)
  :INPUT-CONTRACT
  (AND (|intP|
        |http://sadl.org/Validator.sadl#ResponseID^http://sadl.org/Validator.sadl#uxas__messages__task__UniqueAutomationRequest|))
  :OUTPUT-CONTRACT
  (|uxas__messages__task__UniqueAutomationRequestP|
   (|http://sadl.org/ValidatorReq.sreq#msg_PublishAutomationRequest|
    |http://sadl.org/Validator.sadl#ResponseID^http://sadl.org/Validator.sadl#uxas__messages__task__UniqueAutomationRequest|))
  (|http://sadl.org/ValidatorReq.sreq#msg_PublishAutomationRequest_defstub|
   |http://sadl.org/Validator.sadl#ResponseID^http://sadl.org/Validator.sadl#uxas__messages__task__UniqueAutomationRequest|)))
(IN-THEORY
 (DISABLE
  |http://sadl.org/ValidatorReq.sreq#msg_PublishAutomationRequest|
  (|http://sadl.org/ValidatorReq.sreq#msg_PublishAutomationRequest|)
  |http://sadl.org/ValidatorReq.sreq#msg_PublishAutomationRequest-DEFINITION-RULE|))

; Requirements
(DEFREQUIREMENT |PublishAutomationRequest|
 ((|previous state of AutomationRequestValidatorService|
   |AutomationRequestValidatorServiceStateP|)
  (|automationRequestList of AutomationRequestValidatorService|
   |LIST_OF_1_TO_1_uxas__messages__task__TaskAutomationRequestP|))
 ((|uxas__messages__task__UniqueAutomationRequest_out of AutomationRequestValidatorService|
   |uxas__messages__task__UniqueAutomationRequestP|))
 ((:SRL-NAME . |PublishAutomationRequest|))
 (RIMPLIES
  (AND (EQUAL |previous state of AutomationRequestValidatorService|
              '|Idle|)
       (SRL->
        (LEN-C
         |automationRequestList of AutomationRequestValidatorService|)
        0))
  (EQUAL |uxas__messages__task__UniqueAutomationRequest_out of AutomationRequestValidatorService|
         (|http://sadl.org/ValidatorReq.sreq#msg_PublishAutomationRequest|
          (|http://sadl.org/Validator.sadl#result^http://sadl.org/ValidatorReq.sreq#newid_PublishAutomationRequest|)))))

; Merged Conditional Completeness Form
(SET-RAE-TBL-CONDITIONAL-COMPLETENESS-FORM
 '(((|LIST_OF_1_TO_1_uxas__messages__task__TaskAutomationRequestP|
     |automationRequestList of AutomationRequestValidatorService|)
    (|AutomationRequestValidatorServiceStateP|
     |previous state of AutomationRequestValidatorService|))
   ((NOT (SRL->
          (LEN-C
           |automationRequestList of AutomationRequestValidatorService|)
          0))
    (NOT (EQUAL |previous state of AutomationRequestValidatorService|
                '|Idle|)))))

; No contingency requirement forms
(REGISTER-SRL-NO-CONTINGENCY-REQ |PublishAutomationRequest|)

; No contingency decomposition forms
(REGISTER-SRL-NO-INNER-CONTINGENCY-VAR
 |http://sadl.org/Validator.sadl#result^http://sadl.org/ValidatorReq.sreq#newid_PublishAutomationRequest|)
(REGISTER-SRL-NO-INNER-CONTINGENCY-VAR
 |http://sadl.org/ValidatorReq.sreq#msg_PublishAutomationRequest|)

; No contingency inline equation forms
(REGISTER-SRL-NO-INNER-CONTINGENCY-VAR SRL-ARCCOS)
(REGISTER-SRL-NO-INNER-CONTINGENCY-VAR SRL-ARCCOT)
(REGISTER-SRL-NO-INNER-CONTINGENCY-VAR SRL-ARCCSC)
(REGISTER-SRL-NO-INNER-CONTINGENCY-VAR SRL-ARCSEC)
(REGISTER-SRL-NO-INNER-CONTINGENCY-VAR SRL-ARCSIN)
(REGISTER-SRL-NO-INNER-CONTINGENCY-VAR SRL-ARCTAN)
(REGISTER-SRL-NO-INNER-CONTINGENCY-VAR SRL-COS)
(REGISTER-SRL-NO-INNER-CONTINGENCY-VAR SRL-COT)
(REGISTER-SRL-NO-INNER-CONTINGENCY-VAR SRL-CSC)
(REGISTER-SRL-NO-INNER-CONTINGENCY-VAR SRL-SEC)
(REGISTER-SRL-NO-INNER-CONTINGENCY-VAR SRL-SIN)
(REGISTER-SRL-NO-INNER-CONTINGENCY-VAR SRL-TAN)
(REGISTER-SRL-NO-INNER-CONTINGENCY-VAR SRL-^)

; RAE data
(SET-RAE-TBL-ASSUMPTIONS 'NIL)

; RAE meta data
(SET-RAE-TBL-SRL-REQUIREMENTS-LIST '(|PublishAutomationRequest|))
(SET-RAE-TBL-SRL-ASSUMPTIONS-LIST 'NIL)
(SET-RAE-TBL-SRL-CONTROLLED-VARIABLE
 '|uxas__messages__task__UniqueAutomationRequest_out of AutomationRequestValidatorService|)

