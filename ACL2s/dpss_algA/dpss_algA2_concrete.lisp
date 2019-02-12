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
(include-book "custom" :dir :acl2s-modes :uncertified-okp nil :load-compiled-file :comp)

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
;DPSS CONSTANTS
(defconst *n_int* 3)
(defconst *n_real* 3.)
(defconst *p* 10.)
(defconst *v* 1.)
(defmacro dpss_t () (/ *p* *v*))
(defconst *left* 0)
(defconst *right* 1)
(defconst *left_real* 0.)
(defconst *right_real* 1.)

(defconst *true_int* 1)
(defconst *false_int* 0)

;Convenient definitions for ranges and enums
(defdata bool (range integer (0 <= _ <= 1)))
(defdata direction (enum '(left right)))
(defdata position (range rational (0. <= _ <= *p*)))
(defdata id (range integer (0. < _ <= *n_int*)))
;(defdata state (enum '(null escorted escorting converged)))


;Record (struct) representing single UAV
(defdata UAS (record (uasid . id)
                     (dir . bool)
                     (pre_dir . bool)
                     (loc . position)
                     (pre_loc . position)
                     (goal . position)
                     (pre_goal . position)
                     ;(st . state)
                     (meet_ln . bool)
                     (meet_rn . bool)
                     (s_l . position)
                     (s_r . position)))

;Full system consisting of a list of UAVs
;(defdata system (listof UAS))

;Direction update
(defun set_direction (ag)
  (if (uasp ag)
    (if (<= (uas-pre_loc ag) 0.)
      (set-uas-dir *right* ag)
      (if (>= (uas-pre_loc ag) *p*)
        (set-uas-dir *left* ag)
        (if (= (uas-meet_ln ag) *true_int*)
          (if (<= (uas-pre_loc ag) (uas-pre_loc ag))
            (set-uas-dir *right* ag)
            (set-uas-dir *left* ag))
          (if (= (uas-meet_rn ag) *true_int*)
            (if (<= (uas-pre_loc ag) (uas-s_r ag))
              (set-uas-dir *right* ag)
              (set-uas-dir *left* ag))
            ()))))()))

;Goal update
(defun set_goal (ag)
  (if (uasp ag)
    (if (and (= (uas-meet_ln ag) 1) (= (uas-meet_rn ag) 1))
      (if (<= (uas-pre_loc ag) (uas-s_l ag))
        (set-uas-goal (uas-s_r ag) ag)
        (set-uas-goal (uas-s_l ag) ag))
      (if (= (uas-meet_ln ag) 1)
        (if (<= (uas-pre_loc ag) (uas-s_l ag))
          (set-uas-goal *p* ag)
          (set-uas-goal (uas-s_l ag) ag))
        (if (= (uas-meet_rn ag) 1)
          (if (>= (uas-pre_loc ag) (uas-s_r ag))
            (set-uas-goal 0. ag)
            (set-uas-goal (uas-s_r ag) ag))
          (if (= (uas-pre_dir ag) *right*)
            (set-uas-goal *p* ag)
            (set-uas-goal 0. ag)))))
    ())
  )

;Position update
(defun set_loc (ag dt)
  (if (and (uasp ag) (rationalp dt))
    (if (= (uas-dir ag) *right*)
      (set-uas-loc (+ (uas-loc ag) (* *v* dt)) ag)
      (set-uas-loc (- (uas-loc ag) (* *v* dt)) ag)
      )
    ()
    )
  )

;Getters for record entries
(defun get_direction (ag)
  (if (uasp ag)
    (uas-dir ag)
    ()))

(defun get_goal (ag)
  (if (uasp ag)
    (uas-goal ag)
    ()))

;Utility functions (drawn from AGREE models)
(defun max_rat (a b)
  (if (and (rationalp a) (rationalp b))
    (if (>= a b)
      a
      b
     )
    ()))

(defun min_time (a b)
  (if (and (rationalp a) (rationalp b))
    (if (>= a b)
      b
      a
      )
    ()))

(defun time_to_reach_endpoint (dir loc)
  (if (= dir *right*)
    (/ (- *p* loc) *v*)
    (/ loc *v*)))

(defun time_to_reach_neighbor (dir_uav_1 dir_uav_2 loc_uav_1 loc_uav_2)
  (if (= loc_uav_1 loc_uav_2)
    (dpss_t)
    (if (> loc_uav_2 loc_uav_1)
      (if (and (= dir_uav_1 *right*) (= dir_uav_2 *left*))
        (/ (* (/ 1 2) (- loc_uav_2 loc_uav_1)) *v*)
        (dpss_t))
      (if (and (= dir_uav_1 *left*) (= dir_uav_2 *right*))
        (/ (* (/ 1 2) (- loc_uav_1 loc_uav_2)) *v*)
        (dpss_t)))))

(defun time_to_reach_target_position (dir loc target)
  (if (and (> target loc) (= dir *right*))
    (/ (- target loc) *v*)
    (if (and (< target loc) (= dir *left*))
      (/ (- loc target) *v*)
      (dpss_t))))

(defun delta_t (uas_list)
  (if (listp uas_list)
    (if (= (length uas_list) 0)
      '(100) ;If this is an empty list, return a high number that is likely to get beaten out by the min call
        (min_time (time_to_reach_target_position (mget :dir (first uas_list)) (mget :loc (first uas_list)) (mget :target (first uas_list))) (delta_t (rest uas_list))))
  '(1.)))

(defun delta_t_nums (uas_list)
  (if (listp uas_list)
    (if (= (len uas_list) 0)
      '(100.) ;If this is an empty list, return a high number that is likely to get beaten out by the min call
        (min_time (nth 1 uas_list) (delta_t_nums (nthcdr 1 uas_list))))
  '(1.)))

(defmacro p_12 () (* 1. (/ *p* *n_real*)))
(defmacro p_23 () (* 2. (/ *p* *n_real*)))

(defun optimal? (uas1 uas2 uas3)
  (and (and (uasp uas1) (uasp uas2) (uasp uas3))
    (or (and (and (= (uas-loc uas1) 0.) (= (uas-loc uas2) (p_23)) (= (uas-loc uas3) (p_23)))
             (and (= (uas-pre_loc uas1) (p_12)) (= (uas-loc uas2) (p_12)) (= (uas-loc uas3) *p*)))
        (and (and (= (uas-loc uas1) (p_12)) (= (uas-loc uas2) (p_12)) (= (uas-loc uas3) *p*))
             (and (= (uas-pre_loc uas1) 0.) (= (uas-loc uas2) (p_23)) (= (uas-loc uas3) (p_23)))))
    )
  )

;TODO: how do we update state for the UAS during these recursive calls?

;Recursively evaluates next steps for uavs
(defun DPSS_eval (uas1 uas2 uas3)
    (if (and (uasp uas1) (uasp uas2) (uasp uas3))
      (let ((dt (min_time (time_to_reach_target_position (uas-dir uas1) (uas-loc uas1) (uas-goal uas1))
                     (min_time (time_to_reach_target_position (uas-dir uas2) (uas-loc uas2) (uas-goal uas2))
                               (min_time (time_to_reach_target_position (uas-dir uas3) (uas-loc uas3) (uas-goal uas3))
                                         (min_time (time_to_reach_neighbor (uas-dir uas1) (uas-dir uas2) (uas-loc uas1) (uas-loc uas2))
                                                   (time_to_reach_neighbor (uas-dir uas2) (uas-dir uas3) (uas-loc uas2) (uas-loc uas3))))))))
      (if (optimal? uas1 uas2 uas3)
        '0;termination of recursion: reached optimal state so 'no more important events';recursion: add time to next step ('important event') to recursive call to evaluate
      (progn$
       ;UPDATE STATE HERE
       ;Update previous positions
       (set-uas-pre_loc (uas-loc uas1) uas1)
       (set-uas-pre_loc (uas-loc uas2) uas2)
       (set-uas-pre_loc (uas-loc uas3) uas3)
       ;Update previous directions
       (set-uas-pre_dir (uas-dir uas1) uas1)
       (set-uas-pre_dir (uas-dir uas2) uas2)
       (set-uas-pre_dir (uas-dir uas3) uas3)
       ;Update previous goals
       (set-uas-pre_goal (uas-goal uas1) uas1)
       (set-uas-pre_goal (uas-goal uas2) uas2)
       (set-uas-pre_goal (uas-goal uas3) uas3)
       ;Use the dt we calculated before to "step" all of the UAVs forward
       
       ;Update meet variables if necessary
       (if (= (uas-loc uas1) (uas-loc uas2))
         (progn$
          (set-uas-meet_rn 't uas1)
          (set-uas-meet_ln 't uas2))
         ())
       (if (= (uas-loc uas2) (uas-loc uas3))
         (progn$
          (set-uas-meet_rn 't uas2)
          (set-uas-meet_ln 't uas3))
         ())
       
       ;Step forward UAS1
       (set_direction uas1)
       (set_goal uas1)
       (set_loc uas1 dt)
       
       ;Step forward UAS2
       (set_direction uas2)
       (set_goal uas2)
       (set_loc uas2 dt)
       
       ;Step forward UAS3
       (set_direction uas3)
       (set_goal uas3)
       (set_loc uas3 dt)
       
       ;Print out the updated state information
       (cw "stepping")
       
        (+ dt
           (DPSS_eval uas1 uas2 uas3)
           );evaluate steps
        )
      ))
      '0;if objects passed in aren't uas, evaluate to zero; vacuously satisfies any properties
      )
  )

;Initializes uavs using given initial positions
(defun DPSS (init_pos_uas1 init_pos_uas2 init_pos_uas3 init_dir_uas1 init_dir_uas2 init_dir_uas3)
  (let*  ((uas1 (nth-uas 1))
         (uas2 (nth-uas 1))
         (uas3 (nth-uas 1)))
    (and 
     (set-uas-loc init_pos_uas1 uas1)
    (set-uas-loc init_pos_uas2 uas2)
    (set-uas-loc init_pos_uas3 uas3)
    (set-uas-pre_loc init_pos_uas1 uas1)
    (set-uas-pre_loc init_pos_uas2 uas2)
    (set-uas-pre_loc init_pos_uas3 uas3)
    (set-uas-dir init_dir_uas1 uas1)
    (set-uas-dir init_dir_uas2 uas2)
    (set-uas-dir init_dir_uas3 uas3)
    (set-uas-st nil uas1)
    (set-uas-st nil uas2)
    (set-uas-st nil uas3)
    (set-uas-meet_ln nil uas1)
    (set-uas-meet_ln nil uas2)
    (set-uas-meet_ln nil uas3)
    (set-uas-meet_rn nil uas1)
    (set-uas-meet_rn nil uas2)
    (set-uas-meet_rn nil uas3)
    (set-uas-s_l 0 uas1)
    (set-uas-s_r (p_12) uas1)
    (set-uas-s_l (p_12) uas2)
    (set-uas-s_r (p_23) uas2)
    (set-uas-s_l (p_23) uas3)
    (set-uas-s_r *p* uas3)
    (if (eq (uas-dir uas1) 'right)
      (set-uas-goal *p* uas1)
      (set-uas-goal 0. uas1))
    (if (eq (uas-dir uas2) 'right)
      (set-uas-goal *p* uas2)
      (set-uas-goal 0. uas2))
    (if (eq (uas-dir uas3) 'right)
      (set-uas-goal *p* uas3)
      (set-uas-goal 0. uas3))
    (DPSS_eval uas1 uas2 uas3))
   )
)

(defthm uas_time_bound
  (implies (and (positionp p_uas1) (positionp p_uas2) (positionp p_uas3) (directionp d_uas1) (directionp d_uas2) (directionp d_uas3))
           (<= (DPSS p_uas1 p_uas2 p_uas3 d_uas1 d_uas2 d_uas3)
              (* 2 (dpss_t)))))
