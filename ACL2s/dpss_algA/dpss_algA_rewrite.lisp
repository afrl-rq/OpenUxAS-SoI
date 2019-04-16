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
(defconst *n* 3)
(defconst *p* 10.)
(defconst *v* 1.)
(defconst *dpss_t* (/ *p* *v*))

;Convenient definitions for ranges and enums
(defdata direction (enum '(left right))) ;just aliasing direction to a boolean for ease; 0-left, 1-right
(defdata position (range rational (0. <= _ <= *p*)))
(defdata id (range integer (0. < _ <= *n*)))

;Record (struct) representing single UAV
(defdata UAS (record (uasid . id)
                     (dir . direction)
                     (pre_dir . direction)
                     (loc . position)
                     (pre_loc . position)
                     (goal . position)
                     (pre_goal . position)
                     (meet_ln . boolean)
                     (meet_rn . boolean)
                     (s_l . position)
                     (s_r . position)))

(defunc andm (a b)
  :input-contract (and (booleanp a) (booleanp b))
  :output-contract (booleanp (and a b))
  (if a b nil))#|ACL2s-ToDo-Line|#



;((<= (uas-pre_loc ag) 0.) (UAS (uas-uasid ag) 'right (uas-pre_dir ag) (uas-loc ag) (uas-pre_loc ag) (uas-goal ag) (uas-pre_goal ag) (uas-meet_ln ag) (uas-meet_rn ag) (uas-s_l ag) (uas-s_r ag)))
;        ((>= (uas-pre_loc ag) *p*) (UAS (uas-uasid ag) 'left (uas-pre_dir ag) (uas-loc ag) (uas-pre_loc ag) (uas-goal ag) (uas-pre_goal ag) (uas-meet_ln ag) (uas-meet_rn ag) (uas-s_l ag) (uas-s_r ag)))
;        ((uas-meet_ln ag)
;         (if (<= (uas-pre_loc ag) (uas-s_l ag)) 
;           (UAS (uas-uasid ag) 'right (uas-pre_dir ag) (uas-loc ag) (uas-pre_loc ag) (uas-goal ag) (uas-pre_goal ag) (uas-meet_ln ag) (uas-meet_rn ag) (uas-s_l ag) (uas-s_r ag))
;           (UAS (uas-uasid ag) 'left (uas-pre_dir ag) (uas-loc ag) (uas-pre_loc ag) (uas-goal ag) (uas-pre_goal ag) (uas-meet_ln ag) (uas-meet_rn ag) (uas-s_l ag) (uas-s_r ag))))
;        ((uas-meet_rn ag)
;         (if (< (uas-pre_loc ag) (uas-s_r ag)) 
;           (UAS (uas-uasid ag) 'right (uas-pre_dir ag) (uas-loc ag) (uas-pre_loc ag) (uas-goal ag) (uas-pre_goal ag) (uas-meet_ln ag) (uas-meet_rn ag) (uas-s_l ag) (uas-s_r ag))
;           (UAS (uas-uasid ag) 'left (uas-pre_dir ag) (uas-loc ag) (uas-pre_loc ag) (uas-goal ag) (uas-pre_goal ag) (uas-meet_ln ag) (uas-meet_rn ag) (uas-s_l ag) (uas-s_r ag))))
;Direction update
(defunc set_direction (ag)
  :input-contract (uasp ag)
  :output-contract (uasp (set_direction))
  ;(UAS (uas-uasid ag) (uas-dir ag) (uas-pre_dir ag) (uas-loc ag) (uas-pre_loc ag) (uas-goal ag) (uas-pre_goal ag) (uas-meet_ln ag) (uas-meet_rn ag) (uas-s_l ag) (uas-s_r ag))
  (UAS (uas-uasid ag) 'left 'left 1. 1. 1. 1. nil nil 1. 1.)
)

(defunc set_loc (ag dt)
  :input-contract (and (uasp ag) (rationalp dt) (<= (+ (uas-loc ag) (* *v* dt)) *p*) (> dt 0) (>= (- (uas-loc ag) (* *v* dt)) 0.))
  :output-contract (uasp (set_loc ag dt))
  (if (equal (uas-dir ag) 'right)
    (UAS (uas-uasid ag) (uas-dir ag) (uas-pre_dir ag) (+ (uas-loc ag) (* *v* dt)) (uas-pre_loc ag) (uas-goal ag) (uas-pre_goal ag) (uas-meet_ln ag) (uas-meet_rn ag) (uas-s_l ag) (uas-s_r ag))
    (UAS (uas-uasid ag) (uas-dir ag) (uas-pre_dir ag) (- (uas-loc ag) (* *v* dt)) (uas-pre_loc ag) (uas-goal ag) (uas-pre_goal ag) (uas-meet_ln ag) (uas-meet_rn ag) (uas-s_l ag) (uas-s_r ag)))
)

(defunc set_goal (ag)
  :input-contract (uasp ag)
  :output-contract (uasp ag)
    (if (and (uas-meet_ln ag) (uas-meet_rn ag))
      (if (<= (uas-pre_loc ag) (uas-s_l ag))
        (UAS (uas-uasid ag) (uas-dir ag) (uas-pre_dir ag) (uas-loc ag) (uas-pre_loc ag) (uas-s_r ag) (uas-pre_goal ag) (uas-meet_ln ag) (uas-meet_rn ag) (uas-s_l ag) (uas-s_r ag))
        (UAS (uas-uasid ag) (uas-dir ag) (uas-pre_dir ag) (uas-loc ag) (uas-pre_loc ag) (uas-s_l ag) (uas-pre_goal ag) (uas-meet_ln ag) (uas-meet_rn ag) (uas-s_l ag) (uas-s_r ag)))
      (if (uas-meet_ln ag)
        (if (<= (uas-pre_loc ag) (uas-s_l ag))
          (UAS (uas-uasid ag) (uas-dir ag) (uas-pre_dir ag) (uas-loc ag) (uas-pre_loc ag) *p* (uas-pre_goal ag) (uas-meet_ln ag) (uas-meet_rn ag) (uas-s_l ag) (uas-s_r ag))
          (UAS (uas-uasid ag) (uas-dir ag) (uas-pre_dir ag) (uas-loc ag) (uas-pre_loc ag) (uas-s_l ag) (uas-pre_goal ag) (uas-meet_ln ag) (uas-meet_rn ag) (uas-s_l ag) (uas-s_r ag)))
        (if (uas-meet_rn ag)
          (if (>= (uas-pre_loc ag) (uas-s_r ag))
            (UAS (uas-uasid ag) (uas-dir ag) (uas-pre_dir ag) (uas-loc ag) (uas-pre_loc ag) 0. (uas-pre_goal ag) (uas-meet_ln ag) (uas-meet_rn ag) (uas-s_l ag) (uas-s_r ag))
            (UAS (uas-uasid ag) (uas-dir ag) (uas-pre_dir ag) (uas-loc ag) (uas-pre_loc ag) (uas-s_r ag) (uas-pre_goal ag) (uas-meet_ln ag) (uas-meet_rn ag) (uas-s_l ag) (uas-s_r ag)))
          (if (equal (uas-pre_dir ag) 'right)
            (UAS (uas-uasid ag) (uas-dir ag) (uas-pre_dir ag) (uas-loc ag) (uas-pre_loc ag) *p* (uas-pre_goal ag) (uas-meet_ln ag) (uas-meet_rn ag) (uas-s_l ag) (uas-s_r ag))
            (UAS (uas-uasid ag) (uas-dir ag) (uas-pre_dir ag) (uas-loc ag) (uas-pre_loc ag) 0. (uas-pre_goal ag) (uas-meet_ln ag) (uas-meet_rn ag) (uas-s_l ag) (uas-s_r ag))))))
)

  

(defunc max_rat (a b)
  :input-contract (and (rationalp a) (rationalp b))
  :output-contract (rationalp (max_rat a b))
  (if (>= a b)
    a
    b)
)

(defunc min_time (a b)
  :input-contract (and (rationalp a) (rationalp b))
  :output-contract (rationalp (min_time a b))
  (if (>= a b)
    b
    a
    )
)

(defunc time_to_reach_endpoint (dir loc)
  :input-contract (and (directionp dir) (positionp loc))
  :output-contract (rationalp (time_to_reach_endpoint dir loc))
  (if (equal dir 'right)
    (/ (- *p* loc) *v*)
    (/ loc *v*)))

(defunc time_to_reach_target_position (dir loc target)
  :input-contract (and (directionp dir) (positionp loc) (positionp target))
  :output-contract (rationalp (time_to_reach_target_position dir loc target))
  (if (and (> target loc) (equal dir 'right))
    (/ (- target loc) *v*)
    (if (and (< target loc) (equal dir 'left))
      (/ (- loc target) *v*)
      *dpss_t*)))

(defunc time_to_reach_neighbor (dir_uav_1 dir_uav_2 loc_uav_1 loc_uav_2)
  :input-contract (and (directionp dir_uav_1) (directionp dir_uav_2)
                       (positionp loc_uav_1) (positionp loc_uav_2))
  :output-contract (rationalp (time_to_reach_neighbor dir_uav_1 dir_uav_2 loc_uav_1 loc_uav_2))
  (if (= loc_uav_1 loc_uav_2)
    *dpss_t*
    (if (> loc_uav_2 loc_uav_1)
      (if (and (equal dir_uav_1 'right) (equal dir_uav_2 'left))
        (/ (* (/ 1 2) (- loc_uav_2 loc_uav_1)) *v*)
        *dpss_t*)
      (if (and (equal dir_uav_1 'left) (equal dir_uav_2 'right))
        (/ (* (/ 1 2) (- loc_uav_1 loc_uav_2)) *v*)
        *dpss_t*))))

(defconst *p_12* (* 1. (/ *p* *n*)))
(defconst *p_23* (* 2. (/ *p* *n*)))

(defunc optimal? (uas1 uas2 uas3)
  :input-contract (and (uasp uas1) (uasp uas2) (uasp uas3))
  :output-contract (booleanp (optimal? uas1 uas2 uas3))
  (or (and (and (= (uas-loc uas1) 0.) (= (uas-loc uas2) *p_23*) (= (uas-loc uas3) *p_23*))
             (and (= (uas-pre_loc uas1) *p_12*) (= (uas-loc uas2) *p_12*) (= (uas-loc uas3) *p*)))
        (and (and (= (uas-loc uas1) *p_12*) (= (uas-loc uas2) *p_12*) (= (uas-loc uas3) *p*))
             (and (= (uas-pre_loc uas1) 0.) (= (uas-loc uas2) *p_23*) (= (uas-loc uas3) *p_23*))))
)

;Recursively evaluates next steps for uavs
(defunc DPSS_eval (uas1 uas2 uas3)
  :input-contract (and (uasp uas1) (uasp uas2) (uasp uas3))
  :output-contract (rationalp (DPSS_eval uas1 uas2 uas3))
      (let* ((dt (min_time (time_to_reach_target_position (uas-dir uas1) (uas-loc uas1) (uas-goal uas1))
                     (min_time (time_to_reach_target_position (uas-dir uas2) (uas-loc uas2) (uas-goal uas2))
                               (min_time (time_to_reach_target_position (uas-dir uas3) (uas-loc uas3) (uas-goal uas3))
                                         (min_time (time_to_reach_neighbor (uas-dir uas1) (uas-dir uas2) (uas-loc uas1) (uas-loc uas2))
                                                   (time_to_reach_neighbor (uas-dir uas2) (uas-dir uas3) (uas-loc uas2) (uas-loc uas3))))))))
      (if (optimal? uas1 uas2 uas3)
        0.;termination of recursion: reached optimal state so 'no more important events';recursion: add time to next step ('important event') to recursive call to evaluate
      (let* 
       ;UPDATE STATE HERE
       ;Update previous positions
       ((uas1 (UAS (uas-uasid uas1) (uas-dir uas1) (uas-dir uas1) (uas-loc uas1) (uas-loc uas1) (uas-goal uas1) (uas-goal uas1) (uas-meet_ln uas1) (if (= (uas-loc uas1) (uas-loc uas2)) t nil) (uas-s_l uas1) (uas-s_r uas1)))
       (uas2 (UAS (uas-uasid uas2) (uas-dir uas2) (uas-dir uas2) (uas-loc uas2) (uas-loc uas2) (uas-goal uas2) (uas-goal uas2) (if (= (uas-loc uas1) (uas-loc uas2)) t nil) (if (= (uas-loc uas2) (uas-loc uas3)) t nil) (uas-s_l uas2) (uas-s_r uas2)))
       (uas3 (UAS (uas-uasid uas3) (uas-dir uas3) (uas-dir uas3) (uas-loc uas3) (uas-loc uas3) (uas-goal uas3) (uas-goal uas3) (if (= (uas-loc uas2) (uas-loc uas3)) t nil) (uas-meet_rn uas3) (uas-s_l uas3) (uas-s_r uas3)))
       (uas1 (set_direction uas1))
       (uas1 (set_goal uas1))
       (uas1 (set_loc uas1 dt))
       (uas2 (set_direction uas2))
       (uas2 (set_goal uas2))
       (uas2 (set_loc uas2 dt))
       (uas3 (set_direction uas3))
       (uas3 (set_goal uas3))
       (uas3 (set_loc uas3 dt)))       
       (+ dt (DPSS_eval uas1 uas2 uas3)))
      ))
)

(defunc DPSS (init_pos_uas1 init_pos_uas2 init_pos_uas3 init_dir_uas1 init_dir_uas2 init_dir_uas3)
  :input-contract (and (positionp init_pos_uas1) (positionp init_pos_uas2) (positionp init_pos_uas3)
                       (directionp init_dir_uas1) (directionp init_dir_uas2) (directionp init_dir_uas3))
  :output-contract (rationalp (DPSS init_pos_uas1 init_pos_uas2 init_pos_uas3 init_dir_uas1 init_dir_uas2 init_dir_uas3))
  (let*  ((uas1 (UAS 1 init_dir_uas1 init_dir_uas1 init_pos_uas1 init_pos_uas1 (if (eq init_dir_uas1 'right) *p* 0) (if (eq init_dir_uas1 'right) *p* 0) nil (if (= init_pos_uas1 init_pos_uas2) t nil) 0 *p_12*))
         (uas2 (UAS 2 init_dir_uas2 init_dir_uas2 init_pos_uas2 init_pos_uas2 (if (eq init_dir_uas2 'right) *p* 0) (if (eq init_dir_uas2 'right) *p* 0) (if (= init_pos_uas1 init_pos_uas2) t nil) (if (= init_pos_uas2 init_pos_uas3) t nil) *p_12* *p_23*))
         (uas3 (UAS 3 init_dir_uas3 init_dir_uas3 init_pos_uas3 init_pos_uas3 (if (eq init_dir_uas3 'right) *p* 0) (if (eq init_dir_uas3 'right) *p* 0) (if (= init_pos_uas1 init_pos_uas2) t nil) nil *p_23* *p*)))
    (DPSS_eval uas1 uas2 uas3))
)

(defthm uas_time_bound
  (implies (and (positionp p_uas1) (positionp p_uas2) (positionp p_uas3) (directionp d_uas1) (directionp d_uas2) (directionp d_uas3))
           (<= (DPSS p_uas1 p_uas2 p_uas3 d_uas1 d_uas2 d_uas3)
              (* 2 (dpss_t)))))
