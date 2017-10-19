; RAE Version: 2017-9-16

(IN-PACKAGE "ACL2S")
(DEFTTAG :PROGN!)
(DEFCONST *SRL-DATA-MINIMUM* (- (EXPT 2 31)))
(DEFCONST *SRL-DATA-MAXIMUM* (- (EXPT 2 31) 1))

; Data Definitions
(DEFDATA |uxas__messages__task__TaskAutomationRequest|
 '|Validator.sadl_uxas__messages__task__TaskAutomationRequest_Val_1|)
(IN-THEORY (DISABLE |uxas__messages__task__TaskAutomationRequestP|))
(ADD-DEFAULT-HINTS!
 '((STAGE |uxas__messages__task__TaskAutomationRequestP| 2)))

(DEFDATA |ErrorMsg|
 (ONEOF '|ErrorMsgTooManyRequests| '|ErrorMsgTimeout|))
(IN-THEORY (DISABLE |ErrorMsgP|))
(ADD-DEFAULT-HINTS! '((STAGE |ErrorMsgP| 2)))

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

(DEFDATA |int_0_TO_20| (RANGE INTEGER (0 <= _ <= 20)))

(DEFDATA |boolean| (ONEOF 'TRUE 'FALSE))
(IN-THEORY (DISABLE |booleanP|))
(ADD-DEFAULT-HINTS! '((STAGE |booleanP| 2)))

(DEFDATA |AutomationRequestValidatorServiceState|
 (ONEOF '|Idle| '|Busy|))
(IN-THEORY (DISABLE |AutomationRequestValidatorServiceStateP|))
(ADD-DEFAULT-HINTS!
 '((STAGE |AutomationRequestValidatorServiceStateP| 2)))

(DEFDATA |int_0_TO_11| (RANGE INTEGER (0 <= _ <= 11)))

(DEFDATA |uxas__messages__task__UniqueAutomationResponse|
 '|Validator.sadl_uxas__messages__task__UniqueAutomationResponse_Val_1|)
(IN-THEORY
 (DISABLE |uxas__messages__task__UniqueAutomationResponseP|))
(ADD-DEFAULT-HINTS!
 '((STAGE |uxas__messages__task__UniqueAutomationResponseP| 2)))

(DEFDATA |int|
 (RANGE INTEGER (*SRL-DATA-MINIMUM* <= _ <= *SRL-DATA-MAXIMUM*)))

(DEFTHM |int_0_TO_11-INTEGER-THM|
 (IMPLIES (|int_0_TO_11P| X) (INTEGERP X)))
(DEFTHM |int_0_TO_11-RATIONAL-THM|
 (IMPLIES (|int_0_TO_11P| X) (RATIONALP X)))

(DEFTHM |int_0_TO_20-INTEGER-THM|
 (IMPLIES (|int_0_TO_20P| X) (INTEGERP X)))
(DEFTHM |int_0_TO_20-RATIONAL-THM|
 (IMPLIES (|int_0_TO_20P| X) (RATIONALP X)))

(DEFTHM |int-INTEGER-THM| (IMPLIES (|intP| X) (INTEGERP X)))
(DEFTHM |int-RATIONAL-THM| (IMPLIES (|intP| X) (RATIONALP X)))

; Decomposition Functions
(DEFSTUB |http://sadl.org/ValidatorReq.sreq_DecompVar1_defstub| NIL
 => *)
(SKIP-PROOFS
 (DEFUNC |http://sadl.org/ValidatorReq.sreq_DecompVar1| NIL
  :INPUT-CONTRACT (AND) :OUTPUT-CONTRACT
  (|uxas__messages__task__TaskAutomationRequestP|
   (|http://sadl.org/ValidatorReq.sreq_DecompVar1|))
  (|http://sadl.org/ValidatorReq.sreq_DecompVar1_defstub|)))
(IN-THEORY
 (DISABLE |http://sadl.org/ValidatorReq.sreq_DecompVar1|
  (|http://sadl.org/ValidatorReq.sreq_DecompVar1|)
  |http://sadl.org/ValidatorReq.sreq_DecompVar1-DEFINITION-RULE|))

; Requirements
(DEFREQUIREMENT |AutomationRequestReceived2|
 ((|automationRequestList of AutomationRequestValidatorService|
   |LIST_OF_1_TO_1_uxas__messages__task__TaskAutomationRequestP|)
  (|maxListLength of AutomationRequestValidatorService|
   |int_0_TO_20P|)
  (|previous state of AutomationRequestValidatorService|
   |AutomationRequestValidatorServiceStateP|)
  (|uxas__messages__task__TaskAutomationRequest__Subscription of AutomationRequestValidatorService|
   |uxas__messages__task__TaskAutomationRequestP|)
  (|denialOfService of System| |booleanP|)
  (|timeSinceLastTimerUpdate of AutomationRequestValidatorService|
   |int_0_TO_11P|)
  (|uxas__messages__task__UniqueAutomationResponse__Subscription of AutomationRequestValidatorService|
   |uxas__messages__task__UniqueAutomationResponseP|))
 ((|errorMsg of AutomationRequestValidatorService| |ErrorMsgP|))
 ((:SRL-NAME . |AutomationRequestReceived2|))
 (RIMPLIES
  (BOR
   (AND (NOT (EQUAL |previous state of AutomationRequestValidatorService|
                    '|Busy|))
        (EQUAL |uxas__messages__task__TaskAutomationRequest__Subscription of AutomationRequestValidatorService|
               (|http://sadl.org/ValidatorReq.sreq_DecompVar1|))
        (EQUAL (LEN-C
                |automationRequestList of AutomationRequestValidatorService|)
               |maxListLength of AutomationRequestValidatorService|))
   (AND (EQUAL |uxas__messages__task__TaskAutomationRequest__Subscription of AutomationRequestValidatorService|
               (|http://sadl.org/ValidatorReq.sreq_DecompVar1|))
        (EQUAL (LEN-C
                |automationRequestList of AutomationRequestValidatorService|)
               |maxListLength of AutomationRequestValidatorService|)
        (EQUAL |uxas__messages__task__UniqueAutomationResponse__Subscription of AutomationRequestValidatorService|
               '|http://sadl.org/Validator.sadl#uxas__messages__task__UniqueAutomationResponse|)
        (SRL-<
         |timeSinceLastTimerUpdate of AutomationRequestValidatorService|
         10))
   (AND (NOT (EQUAL |previous state of AutomationRequestValidatorService|
                    '|Busy|))
        (EQUAL |uxas__messages__task__TaskAutomationRequest__Subscription of AutomationRequestValidatorService|
               (|http://sadl.org/ValidatorReq.sreq_DecompVar1|))
        (EQUAL |denialOfService of System| 'TRUE))
   (AND (EQUAL |uxas__messages__task__TaskAutomationRequest__Subscription of AutomationRequestValidatorService|
               (|http://sadl.org/ValidatorReq.sreq_DecompVar1|))
        (EQUAL |denialOfService of System| 'TRUE)
        (EQUAL |uxas__messages__task__UniqueAutomationResponse__Subscription of AutomationRequestValidatorService|
               '|http://sadl.org/Validator.sadl#uxas__messages__task__UniqueAutomationResponse|)
        (SRL-<
         |timeSinceLastTimerUpdate of AutomationRequestValidatorService|
         10)))
  (EQUAL |errorMsg of AutomationRequestValidatorService|
         '|ErrorMsgTooManyRequests|)))

(DEFREQUIREMENT |Timeout|
 ((|previous state of AutomationRequestValidatorService|
   |AutomationRequestValidatorServiceStateP|)
  (|previous timeSinceLastTimerUpdate of AutomationRequestValidatorService|
   |intP|)
  (|uxas__messages__task__UniqueAutomationResponse__Subscription of AutomationRequestValidatorService|
   |uxas__messages__task__UniqueAutomationResponseP|))
 ((|errorMsg of AutomationRequestValidatorService| |ErrorMsgP|))
 ((:SRL-NAME . |Timeout|))
 (RIMPLIES
  (AND (EQUAL |previous state of AutomationRequestValidatorService|
              '|Busy|)
       (OR (NOT (EQUAL |uxas__messages__task__UniqueAutomationResponse__Subscription of AutomationRequestValidatorService|
                       '|http://sadl.org/Validator.sadl#uxas__messages__task__UniqueAutomationResponse|))
           (SRL->=
            |previous timeSinceLastTimerUpdate of AutomationRequestValidatorService|
            10)))
  (EQUAL |errorMsg of AutomationRequestValidatorService|
         '|ErrorMsgTimeout|)))

; Merged Conditional Completeness Form
(SET-RAE-TBL-CONDITIONAL-COMPLETENESS-FORM
 '(((|booleanP| |denialOfService of System|)
    (|int_0_TO_20P|
     |maxListLength of AutomationRequestValidatorService|)
    (|LIST_OF_1_TO_1_uxas__messages__task__TaskAutomationRequestP|
     |automationRequestList of AutomationRequestValidatorService|)
    (|uxas__messages__task__TaskAutomationRequestP|
     |uxas__messages__task__TaskAutomationRequest__Subscription of AutomationRequestValidatorService|))
   ((AND (NOT (EQUAL (LEN-C
                      |automationRequestList of AutomationRequestValidatorService|)
                     |maxListLength of AutomationRequestValidatorService|))
         (NOT (EQUAL |denialOfService of System| 'TRUE)))
    (NOT (EQUAL |uxas__messages__task__TaskAutomationRequest__Subscription of AutomationRequestValidatorService|
                (|http://sadl.org/ValidatorReq.sreq_DecompVar3|))))))

; No contingency requirement forms
(REGISTER-SRL-NO-CONTINGENCY-REQ |AutomationRequestReceived2|)
(REGISTER-SRL-NO-CONTINGENCY-REQ |Timeout|)

; No contingency variable forms
(REGISTER-SRL-NO-INNER-CONTINGENCY-VAR
 |errorMsg of AutomationRequestValidatorService|)
(REGISTER-SRL-NO-INNER-CONTINGENCY-VAR
 |previous state of AutomationRequestValidatorService|)
(REGISTER-SRL-NO-INNER-CONTINGENCY-VAR
 |uxas__messages__task__UniqueAutomationResponse__Subscription of AutomationRequestValidatorService|)

; No contingency decomposition forms
(REGISTER-SRL-NO-INNER-CONTINGENCY-VAR
 |http://sadl.org/ValidatorReq.sreq_DecompVar1|)

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
 '(|AutomationRequestReceived2| |Timeout|))
(SET-RAE-TBL-SRL-ASSUMPTIONS-LIST 'NIL)
(SET-RAE-TBL-SRL-CONTROLLED-VARIABLE
 '|errorMsg of AutomationRequestValidatorService|)

