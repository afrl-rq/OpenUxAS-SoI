; ****************** BEGIN INITIALIZATION FOR ACL2s MODE ****************** ;
; (Nothing to see here!  Your actual file is after this initialization code);

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading the CCG book.~%") (value :invisible))
(include-book "acl2s/ccg/ccg" :uncertified-okp nil :dir :system :ttags ((:ccg)) :load-compiled-file nil);v4.0 change

;Common base theory for all modes.
#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s base theory book.~%") (value :invisible))
(include-book "acl2s/base-theory" :dir :system :ttags :all)


#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "custom" :dir :acl2s-modes :ttags :all)

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem setting up ACL2s mode.") (value :invisible))

;Settings common to all ACL2s modes
(acl2s-common-settings)
;(acl2::xdoc acl2s::defunc) ;; 3 seconds is too much time to spare -- commenting out [2015-02-01 Sun]

(acl2::xdoc acl2s::defunc) ; almost 3 seconds

; Non-events:
;(set-guard-checking :none)

(acl2::in-package "ACL2S")

; ******************* END INITIALIZATION FOR ACL2s MODE ******************* ;
;$ACL2s-SMode$;ACL2s
;DPSS CONSTANTS
(defconst *n_int* 3)
(defconst *p* 10.)
(defconst *v* 1.)
(defconst *dpss_t* (/ *p* *v*))

;Convenient definitions for ranges and enums
(defdata direction (enum '(left right)))
(defdata position (range rational (0. <= _ <= *p*)))
(defdata id (range integer (0. < _ <= *n_int*)))

;Record (struct) representing single UAV
(defdata UAS (record (uasid . id)
                     (dir . boolean)
                     (loc . position)
                     (goal . position)
                     (meet_ln . boolean)
                     (meet_rn . boolean)
                     (s_l . position)
                     (s_r . position)))#|ACL2s-ToDo-Line|#


(acl2s::definec and (a :boolean b :boolean) :boolean
  (if a b nil))

