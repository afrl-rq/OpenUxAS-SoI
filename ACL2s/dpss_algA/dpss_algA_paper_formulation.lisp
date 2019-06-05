; *************** BEGIN INITIALIZATION FOR PROGRAMMING MODE *************** ;
; (Nothing to see here!  Your actual file is after this initialization code);

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading the TRACE* book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
; only load for interactive sessions: 
#+acl2s-startup (include-book "trace-star" :uncertified-okp nil :dir :acl2s-modes :ttags ((:acl2s-interaction)) :load-compiled-file nil);v4.0 change

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading the EVALABLE-LD-PRINTING book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
; only load for interactive sessions: 
#+acl2s-startup (include-book "hacking/evalable-ld-printing" :uncertified-okp nil :dir :system :ttags ((:evalable-ld-printing)) :load-compiled-file nil);v4.0 change


#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%") (value :invisible))
(include-book "acl2s/defunc" :dir :system :uncertified-okp nil :load-compiled-file :comp) ;lets add defunc at least harshrc [2015-02-01 Sun]
(include-book "acl2s/custom" :dir :system :uncertified-okp nil :load-compiled-file :comp)

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading programming mode.") (value :invisible))


(er-progn 
  (program)
  (defun book-beginning () ()) ; to prevent book development
  (set-irrelevant-formals-ok :warn)
  (set-bogus-mutual-recursion-ok :warn)
  (set-ignore-ok :warn)
  (set-verify-guards-eagerness 0)
  (set-default-hints '(("Goal" :error "This depends on a proof, and proofs are disabled in Programming mode.  The session mode can be changed under the \"ACL2s\" menu.")))
  (reset-prehistory t)
  (set-guard-checking :none)
  (set-guard-checking :nowarn)
  (assign evalable-ld-printingp t)
  (assign evalable-printing-abstractions '(list cons))
  (assign triple-print-prefix "; "))
  
(acl2::in-package "ACL2S")

(cw "~@0Programming mode loaded.~%~@1"
      #+acl2s-startup "${NoMoReSnIp}$~%" #-acl2s-startup ""
      #+acl2s-startup "${SnIpMeHeRe}$~%" #-acl2s-startup "")

; **************** END INITIALIZATION FOR PROGRAMMING MODE **************** ;
;$ACL2s-SMode$;Programming
;Turns off strict termination, function contract, and body contract checking in ACL2s mode
;(set-defunc-termination-strictp nil)
;(set-defunc-function-contract-strictp nil)
;(set-defunc-body-contracts-strictp nil)

;Number of UAS
(defconst *n* 3)
;Length of perimeter
(defconst *p* 10)
;Speed of individual UAS
(defconst *v* 1)
;Time to traverse perimeter once for one UAS
(defconst *dpss_t* (/ *p* *v*))

;Directions along line (convenience)
(defdata direction (enum '(left right)))
;Valid location along perimeter
;(Contrast this with getting a new location in function below, which allows leaving perimeter)
(defdata valid_position (range rational (0 <= _ <= *p*)))
(defdata position rational)
;Possible number of UAS that may be on either side of individual
(defdata num_left_right (range integer (0 <= _ < *n*)))
;Index of a particular UAS; convenient when checking for valid states
(defdata index (range integer (0 < _ <= *n*)))

;Record (struct) representing single UAV
(defdata UAS (record (N_li . num_left_right)   ;number of UAS to left
                     (N_ri . num_left_right)   ;number of UAS to right
                     (P_li . position)   ;amount of perimeter on left (= absolute coordinate on line)
                     (P_ri . position)   ;amount of perimeter on right (= *p* - P_li)
                     (dir . direction)         ;direction of travel
                     (goal . valid_position)   ;target destination: useful in events-based model
                     (id . index))) 

(defdata uas_list (listof UAS))
;there is no obvious 'system-level' state; it's just the composition of the constituent UASs (AT LEAST 1)
(defdata uas_system (cons UAS uas_list))
;list of UAS indices; convenient when checking for valid states
(defdata id_list (listof index))

(assign test_sys (list 
    (list   (cons :0TAG 'UAS)
            (cons :DIR 'RIGHT)
            (cons :GOAL *p*)
            (cons :ID 1)
            (cons :N_LI 0)
            (cons :N_RI 2)
            (cons :P_LI 0)
            (cons :P_RI *p*))
    (list   (cons :0TAG 'UAS)
            (cons :DIR 'LEFT)
            (cons :GOAL 0)
            (cons :ID 2)
            (cons :N_LI 1)
            (cons :N_RI 1)
            (cons :P_LI (/ *p* 2))
            (cons :P_RI (/ *p* 2)))
    (list   (cons :0TAG 'UAS)
            (cons :DIR 'LEFT)
            (cons :GOAL 0)
            (cons :ID 3)
            (cons :N_LI 2)
            (cons :N_RI 0)
            (cons :P_LI *p*)
            (cons :P_RI 0))))

;Computes UAS index (1,2,...,*n*), which determines perimeter slice
(definec uas-relative_index (u :uas) :index
  (1+ (uas-N_li u)))

;List membership predicate
(definec in-list (a :all l :tl) :bool
  (and l ;not endp
       (or (equal (first l) a)
           (in-list a (rest l)))))

;Collects the list of IDs for a given system
(definec get-ids (sys :uas_system) :id_list
    (cons (uas-relative_index (first sys)) 
          (if (endp (cdr sys))
            nil
            (get-ids (rest sys)))))

;Recurses through list of ids, checking for duplicates
(definec valid-unique-ids (sys :id_list) :bool
  (or (endp (cdr sys))
      (and (not (in-list (first sys) (rest sys)))
           (valid-unique-ids (rest sys)))))

;----------------------------------
;TEST 1: UNIQUE IDS
(check= 
 (valid-unique-ids 
  (get-ids (@ test_sys))) t)

;--------------------------------
;TEST 2: NON-UNIQUE IDS
(check= 
 (valid-unique-ids 
  (get-ids 
   (list 
    (list   (cons :0TAG 'UAS)
            (cons :DIR 'RIGHT)
            (cons :GOAL *p*)
            (cons :ID 1)
            (cons :N_LI 1)
            (cons :N_RI 2)
            (cons :P_LI 0)
            (cons :P_RI *p*))
    (list   (cons :0TAG 'UAS)
            (cons :DIR 'LEFT)
            (cons :GOAL 0)
            (cons :ID 2)
            (cons :N_LI 1)
            (cons :N_RI 1)
            (cons :P_LI (/ *p* 2))
            (cons :P_RI (/ *p* 2)))
    (list   (cons :0TAG 'UAS)
            (cons :DIR 'LEFT)
            (cons :GOAL 0)
            (cons :ID 3)
            (cons :N_LI 2)
            (cons :N_RI 0)
            (cons :P_LI *p*)
            (cons :P_RI 0))))) nil)

;Unique ids should ensure that removing one element from the list
;totally removes all elements with the same id
(test? (implies (and (uas_systemp sys) (valid-unique-ids sys))
                (not (in-list (uas-relative_index (first sys)) (get-ids sys)))))

;Recurses through system, ensuring every UAS knows the correct number of other UAS
(definec valid-id-sums (sys :uas_system) :bool
  (and (= (+ 1 (uas-N_li (first sys)) (uas-N_ri (first sys)))
              *n*)
       (or (endp (cdr sys)) 
           (valid-id-sums (rest sys)))))
 
;Recurses through system, ensuring every UAS knows the correct perimeter length
(definec valid-per-lens (sys :uas_system) :bool
  (and (= (+ (uas-P_li (first sys)) (uas-P_ri (first sys)))
              *p*)
       (or (endp (cdr sys))
           (valid-per-lens (rest sys)))))

;Convenience: recurses through system, ensuring UAS are ordered by index in the list
;(NOT NECESSARILY SPATIALLY)
(definec valid-ordered (sys :uas_system) :bool
  (or (endp (cdr sys))
      (and (< (uas-relative_index (first sys)) 
              (uas-relative_index (second sys)))
           (valid-ordered (rest sys)))))

;Checks that system has as many UAS as it should
;(By convention, made a function rather than simply inlining in check below)
(definec valid-system-size (sys :uas_system) :bool
  (= (len sys) *n*))

(definec valid-uas-system (sys :uas_system) :bool
  (and (valid-system-size sys) ;checks to ensure system has correct number of UAS
       (valid-id-sums sys) ;check to ensure left & right uas sum correctly
       (valid-ordered sys) ;checks to ensures that UAS are ordered by id (for convenience)
       (valid-per-lens sys);check to ensure perimeters sum correctly
       (valid-unique-ids (get-ids sys)))) ;check to ensure all ids are unique

;get shared left border based on index
(definec uas-s_l (u :uas) :valid_position      
  (* (/ *p* *n*) (1- (uas-relative_index u))))

;get shared right border based on index
(definec uas-s_r (u :uas) :valid_position    
  (* (/ *p* *n*) (uas-relative_index u)))

;TEST 3: Shared Left border of UAS1 is 0
(check= 
 (uas-s_l
  (list   (cons :0TAG 'UAS)
            (cons :DIR 'RIGHT)
            (cons :GOAL *p*)
            (cons :ID 1)
            (cons :N_LI 0)
            (cons :N_RI (- *n* 1))
            (cons :P_LI 0)
            (cons :P_RI *p*)))
  0)

;TEST 4: Shared Right border of UASN is *p*
(check= 
 (uas-s_r
  (list   (cons :0TAG 'UAS)
            (cons :DIR 'RIGHT)
            (cons :GOAL *p*)
            (cons :ID *n*)
            (cons :N_LI (- *n* 1))
            (cons :N_RI 0)
            (cons :P_LI *p*)
            (cons :P_RI 0)))
  *p*)

(defunc get-uas-by-id (id sys)
  :input-contract (and (indexp id) (uas_systemp sys) (in-list id (get-ids sys)))
  :output-contract (and (uasp (get-uas-by-id id sys)) (in-list (get-uas-by-id id sys) sys))
  (if (equal id (uas-relative_index (first sys)))
    (first sys)
    (get-uas-by-id id (rest sys))))

(defunc get-left-neighbor (u sys)
  :input-contract (and (uasp u) (uas_systemp sys) (valid-uas-system sys) (in-list u sys))
  :output-contract (or (not (get-left-neighbor u sys)) (uasp (get-left-neighbor u sys)))
  (let ((uas-id (uas-relative_index u)))
  (if (> uas-id 1) 
    (get-uas-by-id (1- uas-id) sys)
    nil)))
  
(defunc uas-meet_ln (u sys)
  :input-contract (and (uasp u) (uas_systemp sys) (in-list u sys) (valid-uas-system sys))
  :output-contract (booleanp (uas-meet_ln u sys))
  (let ((ln (get-left-neighbor u sys)))
    (if ln
      (equal (uas-P_li u) (uas-P_li ln))
      nil)))

(defunc get-right-neighbor (u sys)
  :input-contract (and (uasp u) (uas_systemp sys) (in-list u sys) (valid-uas-system sys))
  :output-contract (or (not (get-right-neighbor u sys)) (uasp (get-right-neighbor u sys)))
  (if (equal (uas-relative_index u) *n*) 
    nil
    (get-uas-by-id (1+ (uas-relative_index u)) sys)))
  
(defunc uas-meet_rn (u sys)
  :input-contract (and (uasp u) (uas_systemp sys) (in-list u sys) (valid-uas-system sys))
  :output-contract (booleanp (uas-meet_rn u sys))
  (let ((rn (get-right-neighbor u sys)))
    (if rn
      (equal (uas-P_li u) (uas-P_li rn))
      nil)))

(check= 
 (uas-meet_rn
  (list   (cons :0TAG 'UAS)
            (cons :DIR 'RIGHT)
            (cons :GOAL *p*)
            (cons :ID 1)
            (cons :N_LI 0)
            (cons :N_RI 2)
            (cons :P_LI 0)
            (cons :P_RI *p*))
  (list 
   (list   (cons :0TAG 'UAS)
            (cons :DIR 'RIGHT)
            (cons :GOAL *p*)
            (cons :ID 1)
            (cons :N_LI 0)
            (cons :N_RI 2)
            (cons :P_LI 0)
            (cons :P_RI *p*))
   (list   (cons :0TAG 'UAS)
            (cons :DIR 'LEFT)
            (cons :GOAL 0)
            (cons :ID 2)
            (cons :N_LI 1)
            (cons :N_RI 1)
            (cons :P_LI 0)
            (cons :P_RI *p*))
   (list   (cons :0TAG 'UAS)
            (cons :DIR 'LEFT)
            (cons :GOAL 0)
            (cons :ID 3)
            (cons :N_LI 2)
            (cons :N_RI 0)
            (cons :P_LI *p*)
            (cons :P_RI 0)))) t)

;TEST 5: Neighbors share the correct borders
(test? (implies (and (uasp a) 
                     (uasp b) 
                     (uas_systemp sys)
                     (equal (get-left-neighbor b sys) a)
                     (equal (get-right-neighbor a sys) b))
                (= (uas-s_l b) (uas-s_r a))))
  
(defunc get-new-direction (u sys)
  :input-contract (and (uasp u) (uas_systemp sys) (in-list u sys) (valid-uas-system sys))
  :output-contract (directionp (get-new-direction u sys))
  (cond
   ;If at or past left perimeter border, set direction to right
   ((<= (uas-P_li u) 0) 'right)
   ;If at or past the right perimeter border, set direction to left
   ((<= (uas-P_ri u) 0) 'left)
   ;If co-located with left neighbor
   ((uas-meet_ln u sys)
    ;If to the left of the left meeting point
    (if (<= (uas-P_li u) (uas-s_l u))
      'right
      'left))
   ;If co-located with right neighbor
   ((uas-meet_rn u sys)
    ;If to the left of the right meeting point
    (if (< (uas-P_li u) (uas-s_r u))
      ;Then set direction to right
      'right
      ;Else set direction to left
      'left))
   ;Else, don't change direction
   (t (uas-dir u))))

(defunc get-new-P_ri (u dt)
  :input-contract (and (uasp u) (rationalp dt) (>= dt 0)) ;only update location if won't violate perimeter bounds
  :output-contract (positionp (get-new-P_ri u dt)) ;for now, do checking of position for validity at a higher level than here
  ;If moving right
  (if (equal (uas-dir u) 'right)
    ;getting closer to right endpoint
    (- (uas-P_ri u) (* *v* dt))
    ;getting farther from right endpoint
    (+ (uas-P_ri u) (* *v* dt))))

(defunc get-new-P_li (u dt)
  :input-contract (and (uasp u) (rationalp dt) (>= dt 0)) ;only update location if won't violate perimeter bounds
  :output-contract (rationalp (get-new-P_li u dt)) ;for now, do checking of position for validity at a higher level than here
  ;If moving left
  (if (equal (uas-dir u) 'left)
    ;getting closer to left endpoint
    (- (uas-P_li u) (* *v* dt))
    ;getting farther from left endpoint
    (+ (uas-P_li u) (* *v* dt))))

;Get new goal
(defunc get-new-goal (u sys)
  :input-contract (and (uasp u) (uas_systemp sys) (in-list u sys) (valid-uas-system sys))
  :output-contract (valid_positionp (get-new-goal u sys))
  (let ((to_right_boundary (uas-s_r u))
        (to_left_boundary (uas-s_l u)))
    (cond ((and (uas-meet_ln u sys) (uas-meet_rn u sys)) ;if co-located with both neighbors...
           (if (<= (uas-P_li u) (uas-s_l u)) ;then if to the left of shared left boundary
             to_right_boundary ;then set goal to right boundary
             to_left_boundary)) ;else set goal to left boundary
          ((uas-meet_ln u sys) ;if co-located with just left neighbor
           (if (<= (uas-P_li u) (uas-s_l u)) ;then if to the left of shared left boundary
             *p* ;then set goal to right boundary
             to_left_boundary)) ;then set goal to left boundary
          ((uas-meet_rn u sys) ;if co-located with just right neighbor
           (if (>= (uas-P_li u) (uas-s_r u)) ;then if to the right of shared right boundary
             0 ;then set goal to left perimeter endpoint
             to_right_boundary)) ;then set goal to shared right boundary
          (t ;Otherwise,
           (if (equal (uas-dir u) 'right) ;if moving right
             *p* ;then set goal to right perimeter endpoint
             0))))) ;else set goal to left perimeter endpoint

(definec time_to_reach_endpoint (u :uas) :rational
  ;if moving to the right
  (if (equal (uas-dir u) 'right)
    (/ (uas-P_ri u) *v*) ;then return (position - perimeter_length) / velocity
    (/ (uas-P_li u) *v*))) ;else return position / velocity

(definec time_to_reach_goal (u :uas) :rational
  ;if moving towards target
  (let ((goal (uas-goal u))
        (loc (uas-P_li u))
        (dir (uas-dir u)))
    (if (or (and (> goal loc) (equal dir 'right))
            (and (< goal loc) (equal dir 'left)))
      ;then return distance to target over velocity
      (/ (abs (- goal loc)) *v*)
      ;else return time to traverse full perimeter (overestimate?)
      *dpss_t*)))

(defunc time_to_reach_neighbor (u sys)
  :input-contract (and (uasp u) (uas_systemp sys) (in-list u sys) (valid-uas-system sys))
  :output-contract (rationalp (time_to_reach_neighbor u sys))
  (let* ((u-P_li (uas-P_li u))
         (u-dir (uas-dir u))
         (ln (get-left-neighbor u sys))
         (rn (get-right-neighbor u sys))
         (ln-P_li (if ln (uas-P_li ln) nil))
         (rn-P_li (if rn (uas-P_li rn) nil))
         (ln-dir (if ln (uas-dir ln) nil))
         (rn-dir (if rn (uas-dir rn) nil))
         (time_to_l (if (and ln (not (equal ln-P_li u-P_li)) (equal u-dir 'left) (equal ln-dir 'right))
                      (/ (* (/ 1 2) (abs (- ln-P_li u-P_li))) *v*) 
                      *dpss_t*))
         (time_to_r (if (and rn (not (equal rn-P_li u-P_li)) (equal u-dir 'right) (equal rn-dir 'left))
                      (/ (* (/ 1 2) (abs (- rn-P_li u-P_li))) *v*) 
                      *dpss_t*)))
    (min time_to_l time_to_r)))

(defunc compute-individual-dt (u sys)
  :input-contract (and (uasp u) (uas_systemp sys) (in-list u sys) (valid-uas-system sys))
  :output-contract (rationalp (compute-individual-dt u sys))
  (min (time_to_reach_endpoint u) (min (time_to_reach_goal u) (time_to_reach_neighbor u sys))))

(defdata lor (listof rational))
(defdata ne-lor (cons rational lor))

(definec list-min (l :ne-lor) :rational
  (if (endp (cdr l))
    (first l)
    (min (first l) (list-min (rest l)))))

(defunc compute-all-dt (sys i)
  :input-contract (and (uas_systemp sys) (valid-uas-system sys) (natp i) (<= i (len sys)))
  :output-contract (lorp (compute-all-dt sys i))
  (if (= i 0)
    '()
    (cons (compute-individual-dt (nth (1- i) sys) sys) (compute-all-dt sys (- i 1)))))

(defunc compute-dt (sys)
  :input-contract (and (uas_systemp sys) (valid-uas-system sys))
  :output-contract (rationalp (compute-dt sys))
  (list-min (compute-all-dt sys (len sys))))

(defdata prat (range rational (0 <= _)))

(definec move-uas (u :uas dt :prat) :uas
  (set-uas-P_li (get-new-P_li u dt)
   (set-uas-P_ri (get-new-P_ri u dt) u)))

(defunc move-all-uas (sys dt n)
  :input-contract (and (uas_systemp sys) (valid-uas-system sys) (pratp dt))
  :output-contract (uas_systemp sys)
  (if (= n 1)
    (list (move-uas (nth (1- n) sys) dt))
    (append (move-all-uas sys dt (1- n)) (list (move-uas (nth (1- n) sys) dt)))))

(defunc compute-all-step (sys dt n)
  :input-contract (and (uas_systemp sys) (valid-uas-system sys) (rationalp dt) (>= dt 0) (natp n) (<= n (len sys)))
  :output-contract (uas_systemp (compute-all-step sys dt n))
  (if (= n 1)
    (list (set-uas-goal (get-new-goal (nth (1- n) sys) sys)
                  (set-uas-dir (get-new-direction (nth (1- n) sys) sys) (nth (1- n) sys))))
    (append (compute-all-step sys dt (1- n))
            (list (set-uas-goal (get-new-goal (nth (1- n) sys) sys)
                  (set-uas-dir (get-new-direction (nth (1- n) sys) sys) (nth (1- n) sys)))))))

(defunc step_forward (sys)
  :input-contract (and (uas_systemp sys) (valid-uas-system sys))
  :output-contract (and (uas_systemp (step_forward sys)) (valid-uas-system (step_forward sys)))
  (let* ((dt (compute-dt sys))
         (sys~ (move-all-uas sys dt (len sys))))
    (compute-all-step sys~ dt (len sys~))))

(defunc step_forward_n (sys n)
  :input-contract (and (uas_systemp sys) (valid-uas-system sys) (natp n))
  :output-contract t
  (if (= n 0)
    sys
    (let* ((sys~ (step_forward sys)))
      (cons sys~ (step_forward_n sys~ (1- n))))))#|ACL2s-ToDo-Line|#


;Proof strategy for valid positions:
;Show that all initial configurations are valid
;Show that only valid configurations can be reached by a call to step_forward
;from an already valid configuration
