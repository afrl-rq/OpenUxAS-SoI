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
(defdata state (enum '(null escorted escorting converged)))


;Record (struct) representing single UAV
(defdata UAS (record (uasid . id)
                     (dir . bool)
                     (loc . position)
                     (goal . position)
                     (st . state)
                     (meet_ln . bool)
                     (meet_rn . bool)
                     (s_l . position)
                     (s_r . position)))

;Full system consisting of a list of UAVs
(defdata system (listof UAS))

;Direction update function
(defun set_direction (ag)
  (if (uasp ag)
    (if (<= (uas-loc ag) 0.)
      (set-uas-dir *right* ag)
      (if (>= (uas-loc ag) *p*)
        (set-uas-dir *left* ag)
        (if (= (uas-meet_ln ag) *true_int*)
          (if (<= (uas-loc ag) (uas-loc ag))
            (set-uas-dir *right* ag)
            (set-uas-dir *left* ag))
          (if (= (uas-meet_rn ag) *true_int*)
            (if (<= (uas-loc ag) (uas-s_r ag))
              (set-uas-dir *right* ag)
              (set-uas-dir *left* ag))
            ()))))()))

;Goal update function
(defun set_goal (ag)
  (if (uasp ag)
    (if (and (= (uas-meet_ln ag) 1) (= (uas-meet_rn ag) 1))
      (if (<= (uas-loc ag) (uas-s_l ag))
        (set-uas-goal (uas-s_r ag) ag)
        (set-uas-goal (uas-s_l ag) ag))
      (if (= (uas-meet_ln ag) 1)
        (if (<= (uas-loc ag) (uas-s_l ag))
          (set-uas-goal *p* ag)
          (set-uas-goal (uas-s_l ag) ag))
        (if (= (uas-meet_rn ag) 1)
          (if (>= (uas-loc ag) (uas-s_r ag))
            (set-uas-goal 0. ag)
            (set-uas-goal (uas-s_r ag) ag))
          (if (= (uas-dir ag) *right*)
            (set-uas-goal *p* ag)
            (set-uas-goal 0. ag)))))
    ())
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
      '(100) ;If this is an empty list, return a high number that is likely to get beaten out by the min call
        (min_time (nth 1 uas_list) (delta_t_nums (nthcdr 1 uas_list))))
  '(1.)))

(defmacro p_12 () (* 1. (/ *p* *n_real*)))
(defmacro p_23 () (* 2. (/ *p* *n_real*)))

;Recursively evaluates next steps for uavs
(defun DPSS_eval (uas1 uas2 uas3)
  (if (and (uasp uas1) (uasp uas2) (uasp uas3))
    (mget :goal uas1)
    ()))

;Initializes uavs using given initial positions
(defun DPSS (init_pos_uas1 init_pos_uas2 init_pos_uas3 init_dir_uas1 init_dir_uas2 init_dir_uas3)
  (let*  ((uas1 (nth-uas 1))
         (uas2 (nth-uas 1))
         (uas3 (nth-uas 1)))
    (and (set-uas-loc init_pos_uas1 uas1)
    (set-uas-loc init_pos_uas2 uas2)
    (set-uas-loc init_pos_uas3 uas3)
    (set-uas-loc init_dir_uas1 uas1)
    (set-uas-loc init_dir_uas2 uas2)
    (set-uas-loc init_dir_uas3 uas3)
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

;CONCRETE PROOF (uses n to create concrete number of UAVs)
(defmacro time_to_reach_neighbor_12 () )

