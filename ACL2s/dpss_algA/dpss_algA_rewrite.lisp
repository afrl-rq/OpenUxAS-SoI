; ****************** BEGIN INITIALIZATION FOR ACL2s MODE ****************** ;
; (Nothing to see here!  Your actual file is after this initialization code);
(make-event
 (er-progn
  (set-deferred-ttag-notes t state)
  (value '(value-triple :invisible))))

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading the CCG book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/ccg/ccg" :uncertified-okp nil :dir :system :ttags ((:ccg)) :load-compiled-file nil);v4.0 change

;Common base theory for all modes.
#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s base theory book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/base-theory" :dir :system :ttags :all)


#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/custom" :dir :system :ttags :all)

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
;Assumption: all updates occur in parallel (accomplished through lets)

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

;Direction update
;Note: Pre dir is now updated here also
(defunc set_direction (ag)
  :input-contract (uasp ag)
  :output-contract (uasp (set_direction ag))
  (let* ((ag~ (set-uas-pre_dir (uas-dir ag) ag)))
    (cond
     ;If at or past left perimeter border, set direction to right
     ((<= (uas-loc ag~) 0.) (set-uas-dir 'right ag~))
     ;If at or past the right perimeter border, set direction to left
     ((>= (uas-loc ag~) *p*) (set-uas-dir 'left ag~))
     ;If co-located with left neighbor
     ((uas-meet_ln ag~)
      ;If to the left of the left meeting point
      (if (<= (uas-loc ag~) (uas-s_l ag~))
        ;Then set direction to right
        (set-uas-dir 'right ag~)
        ;Else set direction to left
        (set-uas-dir 'left ag~)))
     ;If co-located with right neighbor
     ((uas-meet_rn ag~)
      ;If to the left of the right meeting point
      (if (< (uas-loc ag~) (uas-s_r ag~))
        ;Then set direction to right
        (set-uas-dir 'right ag~)
        ;Else set direction to left
        (set-uas-dir 'left ag~)))
     ;Else, don't change direction
     (t ag~))))
   
;Test: pre-dir should be equal to the previous direction
(test? (implies (uasp ag)
                (equal (uas-dir ag) (uas-pre_dir (set-direction ag)))))

;Location Update
;Simply based on velocity, direction, length of dt, and current position
;TODO: use a macro for the bounds checking in the input contract and function body (improve readability)
(defunc set_loc (ag dt)
  :input-contract (and (uasp ag) (rationalp dt) (<= (+ (uas-loc ag) (* *v* dt)) *p*) (> dt 0) (>= (- (uas-loc ag) (* *v* dt)) 0.))
  :output-contract (uasp (set_loc ag dt))
  (let* ((ag~ (set-uas-pre_loc (uas-pre_loc ag) ag)))
    ;If moving right
    (if (equal (uas-dir ag~) 'right)
      ;Increment location by (v * dt) 
      (set-uas-loc (+ (uas-loc ag~) (* *v* dt)) ag~)
      ;Decrement location by (v * dt)
      (set-uas-loc (- (uas-loc ag~) (* *v* dt)) ag~))))

;Goal update
;TODO: consider using cond, or something else to reduce this nested if structure
(defunc set_goal (ag)
  :input-contract (uasp ag)
  :output-contract (uasp ag)
  (let* ((ag~ (set-uas-pre_goal (uas-goal ag) ag)))
    ;if co-located with left and right UAVs
    (if (and (uas-meet_ln ag~) (uas-meet_rn ag~))
      ;If the located to the left of the left boundary point
      (if (<= (uas-loc ag~) (uas-s_l ag~))
        ;Set goal to right boundary point
        (set-uas-goal (uas-s_r ag~) ag~)
        ;Set goal to left boundary point
        (set-uas-goal (uas-s_l ag~) ag~))
      ;If co-located with left neighbor
      (if (uas-meet_ln ag~)
        ;If to the left of the left boundary point
        (if (<= (uas-loc ag~) (uas-s_l ag~))
          ;Set the goal to the right perimeter edge
          (set-uas-goal *p* ag~)
          ;Set the goal to the left boundary point
          (set-uas-goal 0 ag~))
        ;If co-located with right neighbor
        (if (uas-meet_rn ag~)
          ;If to the right of the right boundary point
          (if (>= (uas-loc ag~) (uas-s_r ag~))
            ;Set the goal to the left perimeter edge
            (set-uas-goal 0 ag~)
            ;Set the goal to the right boundary point
            (set-uas-goal (uas-s_r ag~) ag~))
          ;If moving to the right
          (if (equal (uas-dir ag~) 'right)
            ;Set the goal to the right perimeter edge
            (set-uas-goal *p* ag~)
            ;Set the goal to the left perimeter edge
            (set-uas-goal 0 ag~)))))))

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
             (and (= (uas-pre_loc uas1) 0.) (= (uas-loc uas2) *p_23*) (= (uas-loc uas3) *p_23*)))))

(defdata lou (listof UAS))
(defdata lon (listof nat))

(definec get-ids (l :lou) :lon
  (if (endp l)
    l
    (cons (uas-uasid (first l)) (get-ids (rest l)))))

;TODO: add predicate for checking that list of UAS has all exclusive ids

;Recursively evaluates next steps for uavs
(defunc DPSS_eval (uas1 uas2 uas3)
  :input-contract (and (uasp uas1) (uasp uas2) (uasp uas3))
  :output-contract (rationalp (DPSS_eval uas1 uas2 uas3))
      (let* ((dt (min (time_to_reach_target_position (uas-dir uas1) (uas-loc uas1) (uas-goal uas1))
                     (min (time_to_reach_target_position (uas-dir uas2) (uas-loc uas2) (uas-goal uas2))
                               (min (time_to_reach_target_position (uas-dir uas3) (uas-loc uas3) (uas-goal uas3))
                                         (min (time_to_reach_neighbor (uas-dir uas1) (uas-dir uas2) (uas-loc uas1) (uas-loc uas2))
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
