; RAE Version: 2017-9-16

(IN-PACKAGE "ACL2S")
(DEFTTAG :PROGN!)
(DEFCONST *SRL-DATA-MINIMUM* (- (EXPT 2 31)))
(DEFCONST *SRL-DATA-MAXIMUM* (- (EXPT 2 31) 1))

; Data Definitions
(DEFDATA |int_0_TO_11| (RANGE INTEGER (0 <= _ <= 11)))

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

(DEFDATA |AutomationRequestValidatorServiceState|
 (ONEOF '|Idle| '|Busy|))
(IN-THEORY (DISABLE |AutomationRequestValidatorServiceStateP|))
(ADD-DEFAULT-HINTS!
 '((STAGE |AutomationRequestValidatorServiceStateP| 2)))

(DEFDATA |int|
 (RANGE INTEGER (*SRL-DATA-MINIMUM* <= _ <= *SRL-DATA-MAXIMUM*)))

(DEFDATA |uxas__messages__task__UniqueAutomationResponse|
 '|Validator.sadl_uxas__messages__task__UniqueAutomationResponse_Val_1|)
(IN-THEORY
 (DISABLE |uxas__messages__task__UniqueAutomationResponseP|))
(ADD-DEFAULT-HINTS!
 '((STAGE |uxas__messages__task__UniqueAutomationResponseP| 2)))

(DEFTHM |int-INTEGER-THM| (IMPLIES (|intP| X) (INTEGERP X)))
(DEFTHM |int-RATIONAL-THM| (IMPLIES (|intP| X) (RATIONALP X)))

(DEFTHM |int_0_TO_11-INTEGER-THM|
 (IMPLIES (|int_0_TO_11P| X) (INTEGERP X)))
(DEFTHM |int_0_TO_11-RATIONAL-THM|
 (IMPLIES (|int_0_TO_11P| X) (RATIONALP X)))

; Requirements
(DEFREQUIREMENT |PublishAutomationRequest|
 ((|previous state of AutomationRequestValidatorService|
   |AutomationRequestValidatorServiceStateP|)
  (|automationRequestList of AutomationRequestValidatorService|
   |LIST_OF_1_TO_1_uxas__messages__task__TaskAutomationRequestP|))
 ((|timeSinceLastTimerUpdate of AutomationRequestValidatorService|
   |int_0_TO_11P|))
 ((:SRL-NAME . |PublishAutomationRequest|))
 (RIMPLIES
  (AND (EQUAL |previous state of AutomationRequestValidatorService|
              '|Idle|)
       (SRL->
        (LEN-C
         |automationRequestList of AutomationRequestValidatorService|)
        0))
  (EQUAL |timeSinceLastTimerUpdate of AutomationRequestValidatorService|
         0)))

(DEFREQUIREMENT |ResponseReceived|
 ((|previous state of AutomationRequestValidatorService|
   |AutomationRequestValidatorServiceStateP|)
  (|previous timeSinceLastTimerUpdate of AutomationRequestValidatorService|
   |intP|)
  (|uxas__messages__task__UniqueAutomationResponse__Subscription of AutomationRequestValidatorService|
   |uxas__messages__task__UniqueAutomationResponseP|))
 ((|timeSinceLastTimerUpdate of AutomationRequestValidatorService|
   |int_0_TO_11P|))
 ((:SRL-NAME . |ResponseReceived|))
 (RIMPLIES
  (AND (EQUAL |previous state of AutomationRequestValidatorService|
              '|Busy|)
       (EQUAL |uxas__messages__task__UniqueAutomationResponse__Subscription of AutomationRequestValidatorService|
              '|http://sadl.org/Validator.sadl#uxas__messages__task__UniqueAutomationResponse|)
       (SRL-<=
        |previous timeSinceLastTimerUpdate of AutomationRequestValidatorService|
        10))
  (EQUAL |timeSinceLastTimerUpdate of AutomationRequestValidatorService|
         0)))

(DEFREQUIREMENT |Timeout|
 ((|previous state of AutomationRequestValidatorService|
   |AutomationRequestValidatorServiceStateP|)
  (|previous timeSinceLastTimerUpdate of AutomationRequestValidatorService|
   |intP|)
  (|uxas__messages__task__UniqueAutomationResponse__Subscription of AutomationRequestValidatorService|
   |uxas__messages__task__UniqueAutomationResponseP|))
 ((|timeSinceLastTimerUpdate of AutomationRequestValidatorService|
   |int_0_TO_11P|))
 ((:SRL-NAME . |Timeout|))
 (RIMPLIES
  (AND (EQUAL |previous state of AutomationRequestValidatorService|
              '|Busy|)
       (OR (NOT (EQUAL |uxas__messages__task__UniqueAutomationResponse__Subscription of AutomationRequestValidatorService|
                       '|http://sadl.org/Validator.sadl#uxas__messages__task__UniqueAutomationResponse|))
           (SRL->=
            |previous timeSinceLastTimerUpdate of AutomationRequestValidatorService|
            10)))
  (EQUAL |timeSinceLastTimerUpdate of AutomationRequestValidatorService|
         0)))

; Merged Conditional Completeness Form
(SET-RAE-TBL-CONDITIONAL-COMPLETENESS-FORM
 '(((|LIST_OF_1_TO_1_uxas__messages__task__TaskAutomationRequestP|
     |automationRequestList of AutomationRequestValidatorService|))
   ((EQUAL (LEN-C
            |automationRequestList of AutomationRequestValidatorService|)
           0))))

; No contingency requirement forms
(REGISTER-SRL-NO-CONTINGENCY-REQ |PublishAutomationRequest|)
(REGISTER-SRL-NO-CONTINGENCY-REQ |ResponseReceived|)
(REGISTER-SRL-NO-CONTINGENCY-REQ |Timeout|)

; No contingency variable forms
(REGISTER-SRL-NO-INNER-CONTINGENCY-VAR
 |previous state of AutomationRequestValidatorService|)
(REGISTER-SRL-NO-INNER-CONTINGENCY-VAR
 |uxas__messages__task__UniqueAutomationResponse__Subscription of AutomationRequestValidatorService|)

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
(SET-RAE-TBL-SRL-REQUIREMENTS-LIST
 '(|PublishAutomationRequest| |ResponseReceived| |Timeout|))
(SET-RAE-TBL-SRL-ASSUMPTIONS-LIST 'NIL)
(SET-RAE-TBL-SRL-CONTROLLED-VARIABLE
 '|timeSinceLastTimerUpdate of AutomationRequestValidatorService|)

