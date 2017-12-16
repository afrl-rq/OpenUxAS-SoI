theory WaypointManagerFunSpec imports 
Main
Sublist
"~~/src/HOL/Library/Multiset"
begin

locale WaypointManager =
  fixes get_number :: "'w \<Rightarrow> 'id"
  fixes get_nextwp :: "'w \<Rightarrow> 'id"
  fixes update_nextwp :: "'w \<Rightarrow> 'id \<Rightarrow> 'w"
  assumes correct_update1[simp,intro]:"get_nextwp (update_nextwp w i) = i"
  and correct_update2[simp,intro]:"get_number (update_nextwp w i) = get_number w"
  and correct_update3[simp,intro]:"get_nextwp w = i \<Longrightarrow> w = update_nextwp w i"
    
context WaypointManager begin

(* FUNSPEC(find_wp): Find a waypoint in a list of waypoints by its number. This is how we 
   notionally expect the find_wp function to work. *)
definition find_waypoint :: "'w list \<Rightarrow> 'id \<Rightarrow> 'w option" where
"find_waypoint ws i \<equiv> List.find (\<lambda> w. get_number w = i) ws" 
      
(* Extending the waypoint list by an uninteresting waypoint preserve find_waypoint failure. *)
lemma find_waypoint_none_extend: 
"None = find_waypoint ws i \<Longrightarrow> get_number w \<noteq> i  \<Longrightarrow> None = find_waypoint (ws @[w]) i"
  apply(induct ws) using find_waypoint_def by auto
  
(* Extending the waypoint list by any waypoint preserves find_waypoint success. *)
lemma find_waypoint_none_extend_some: 
"None = find_waypoint ws i \<Longrightarrow> get_number w = i \<Longrightarrow> Some w = find_waypoint (ws @[w]) i"
  apply(induct ws) using find_waypoint_def by auto     
 
(* Lift find_waypoint properties to a nice FOL formula. *)   
lemma find_waypoint_succuss:
  "Some w = find_waypoint ws i \<Longrightarrow> \<exists> j. j < length ws \<and> w = ws ! j \<and> i = get_number w"
  apply(induct ws)
   apply (simp add: find_waypoint_def)
    by (metis (mono_tags, lifting) find_Some_iff find_waypoint_def)    

(* Lift find_waypoint properties to a nice FOL formula. *)  
lemma find_waypoint_failure_not_equal_all_elems:
  "None = find_waypoint ws n \<Longrightarrow> \<forall> i < length ws. get_number (ws ! i) \<noteq> n"
proof(induct ws)
  case Nil
  then show ?case by auto
next
  case (Cons a ws)
  then have "None = find_waypoint ws n \<and> get_number a \<noteq> n"
    by (metis (mono_tags) find_waypoint_def find.simps(2) option.distinct(1))
  then show ?case 
    using Cons by (metis Suc_less_eq gr0_conv_Suc length_Cons not_gr_zero nth_Cons_0 nth_Cons_Suc)
qed 

(* If a list L1 is a prefix of another L2, that list can be extended by some other list such 
   that it results L2. *)
lemma prefix_ident: "prefix ws' ws \<Longrightarrow> \<exists> ws1. ws = ws'@ws1"
apply (induct ws' arbitrary: ws) using prefix_def by blast+
  
(* If a waypoint is found in a prefix L1 the same waypoint will be found in L2. *)
lemma find_waypoint_ignores_dup_matches:
  "prefix ws' ws \<Longrightarrow> Some w = find_waypoint ws' n \<Longrightarrow> Some w = find_waypoint ws n"
proof(induct ws' arbitrary: ws)
  case Nil
  then show ?case using find_waypoint_def by auto
next
  case (Cons w' ws'')
  then obtain ws1 where y1:"ws = w' # ws'' @ ws1" by (metis append_Cons prefix_ident Cons)
  thus ?case using Cons y1 by (metis Sublist.Cons_prefix_Cons find.simps(2) find_waypoint_def)
qed

(* A condition ensure the first waypoint in the list is always found. *) 
lemma find_waypoint_next_is_match:
assumes a1:"Some w = find_waypoint ws (get_number (ws ! j))"
and  a2:"None = find_waypoint (take j ws) (get_number (ws ! j))"
and a3:"j < length ws"
shows "ws ! j  = w"
proof -
  have "prefix (take j ws) ws" using take_is_prefix by blast
  then have y2:"Some w = find_waypoint (take j ws @ [ws ! j]) (get_number (ws ! j))"
    by (metis (no_types, lifting) a2  find_waypoint_none_extend_some 
        a1 a3 find_waypoint_ignores_dup_matches hd_drop_conv_nth take_hd_drop take_is_prefix)
  thus ?thesis by (metis find_waypoint_none_extend_some a2 option.inject)
qed

(* A successful find returns something sensible. *)
lemma find_waypoint_success_id:"Some w = find_waypoint ws i \<Longrightarrow> get_number w = i"
  apply(induct ws arbitrary: w)
  apply (simp add: find_waypoint_def)
  using find_waypoint_succuss by blast

(* If we find a waypoint then there is a prefix where we cant find the waypoint. *)
lemma find_waypoint_success_construction:
  "Some w = find_waypoint ws i \<Longrightarrow> (\<exists> ws' ws''. ws'@ w # ws'' = ws \<and> None = find_waypoint ws' i)"
proof(induct ws arbitrary: w i)
  case Nil
  then show ?case by (simp add: find_waypoint_def)
next
  case (Cons a ws)
  then have "a = w \<or> a \<noteq> w" by auto
  thus ?case
  proof
    assume "a = w"
    thus ?case using Cons find_waypoint_def by fastforce
  next
    assume "a \<noteq> w"
    thus ?case using Cons find_waypoint_def by (metis append_Cons find.simps(2) option.inject)
  qed
qed

(* Alternate formalization that find_waypoint is a function. *)
lemma find_waypoint_disaggree_absurd:
  "None = find_waypoint ws i \<Longrightarrow> Some w = find_waypoint ws i \<Longrightarrow> False" by auto  
  
(* Whatever find_waypoints finds is in the list. *)
lemma find_waypoint_success_membership:"Some w = find_waypoint ws i \<Longrightarrow> List.member ws w"
  using WaypointManager.find_waypoint_success_construction in_set_member WaypointManager_axioms 
  by fastforce
  
(* If a waypoint is found it's id exists in the multiset of all waypoint id's in the 
 * waypoint list. *)    
lemma find_waypoint_success_mset_membership:
  "Some w = find_waypoint ws i \<Longrightarrow> (get_number w) \<in># mset (map get_number ws)"
  apply(induct ws arbitrary: i w)
    apply (auto simp add: find_waypoint_def)
     by (metis find_Some_iff option.inject)

lemma find_waypoint_success_set_membership:
  "Some w = find_waypoint ws i \<Longrightarrow> (get_number w) \<in> set (map get_number ws)"
  apply(induct ws arbitrary: i w)
    apply (auto simp add: find_waypoint_def)
     by (metis  option.inject)

(* Find waypoint returns a waypoint with the proper id. *)
lemma find_waypoint_correct:"find_waypoint ws i = Some w \<Longrightarrow> get_number w = i"
  apply(induct ws)
   apply (simp add: find_waypoint_def)
  by (metis find_waypoint_success_id)
    
(* If a waypoint can be founnd, the waypoint can still be found in an extend waypoint list. *)    
lemma find_waypoint_extend:"find_waypoint ws i = Some w \<Longrightarrow> \<exists> w'. find_waypoint (a#ws) i = Some w'"
  by (simp add: find_waypoint_def)
    
(* Well-formed waypoint lists: The next waypoint for all waypoints must be findable in the list. *)
definition waypoints_wf where
  "waypoints_wf ws \<equiv> 
  (\<forall> w'. List.member ws w' \<longrightarrow> (\<exists> w. Some w = find_waypoint ws (get_nextwp w')))"
  
(* A lemma exposing the details of the waypoints_wf definition. *)
lemma waypoints_wf_result:
  "waypoints_wf ws \<Longrightarrow> List.member ws w' \<Longrightarrow> (\<exists> w. Some w = find_waypoint ws (get_nextwp w'))"
  using waypoints_wf_def by auto
     
(* Some odd behavior:
  - By definition of this function, cycles in the incoming 'w list will be unrolled in the output
    window. This means that there may be multiple waypoints in the same window with the same number.
    Thus we cannot demand wellformed windows have the property:
      (\<forall> w'. List.member (tl ws) w' \<longrightarrow>  (\<exists> w. Some w' = find_waypoint ws (get_nextwp w)))
*)
  
(* Create a waypoint list segment of some specificied size n by follow the waypoint next id 
 * n times. *)
fun waypoints_window_aux :: "'w list \<Rightarrow> 'id \<Rightarrow> nat \<Rightarrow> ('w list) option" where
"waypoints_window_aux ws i 0 = None"
|"waypoints_window_aux ws i (Suc 0) = 
  (case find_waypoint ws i of 
    None \<Rightarrow> None 
    | Some w \<Rightarrow> Some [w])"
|"waypoints_window_aux ws i (Suc (Suc n)) = 
  (case find_waypoint ws i of 
    None \<Rightarrow> None 
    | Some w \<Rightarrow> 
          (case waypoints_window_aux ws (get_nextwp w) (Suc n) of
            None \<Rightarrow> None
            | Some win \<Rightarrow> Some (w # win)))"
  
(* The head of the segment corresponds to the return value of a particular invocation of 
 * find_waypoint. *)
lemma waypoint_window_aux_find_waypoint_hd:
 "waypoints_window_aux ws i len = Some win \<Longrightarrow> Some (hd (win)) = find_waypoint ws i"
  apply (induct rule:waypoints_window_aux.induct)
    by (auto split: option.splits)

(* If we get a segment then it has at least one waypoint in it. *)
lemma  waypoint_window_aux_success_len_nonzero:
 "waypoints_window_aux ws i len = Some win \<Longrightarrow> 0 < len"
  apply (induct len)
  by (auto split: option.splits)
  
(* Waypoint list will never be empty. *)
lemma waypoint_window_aux_success_len_nonempty: 
  assumes a:"waypoints_window_aux ws i len = Some []" shows " False"
  apply(cases rule:waypoints_window_aux.elims[OF a])
  by (auto split: option.splits)

(* Unroll the head of segments of size two or greater. *)
lemma waypoints_window_aux_success_more_than_one:
  "waypoints_window_aux ws i (Suc (Suc n)) = Some win \<Longrightarrow> 
    find_waypoint ws i = Some (hd win) 
    \<and> waypoints_window_aux ws (get_nextwp (hd win)) (Suc n) = Some (tl win)"
  apply(cases rule:waypoints_window_aux.elims)
  by (auto split:option.splits)

(* Successful segment with size of one. *)    
lemma waypoints_window_aux_success_just_one:
  "waypoints_window_aux ws i (Suc 0) = Some win \<Longrightarrow> \<exists> w. find_waypoint ws i = Some w \<and> win = [w]"
  apply(cases rule:waypoints_window_aux.elims)
  by (auto split:option.splits)

(* Succesful segment has exactly it's specificied length. *)    
lemma waypoints_window_aux_success_length:
  "waypoints_window_aux ws i len = Some win \<Longrightarrow> length win = len"
proof (induct len arbitrary:i win)
  case 0
  then show ?case by auto
next
  case (Suc len)
  have "0 = len \<or> 0 < len" by auto
  thus ?case
  proof
    assume y1:"0 = len"
    then have y2:"waypoints_window_aux ws i (Suc 0) = Some win" using Suc by auto
    obtain w where "win = [w]" using waypoints_window_aux_success_just_one[OF y2] by auto
    thus ?case using y1 by simp
  next
    assume y1:"0 < len"
    then obtain len' where y2:"len = Suc len'"
      using gr0_implies_Suc by blast
    then have y3:"find_waypoint ws i = Some (hd win) 
      \<and> waypoints_window_aux ws (get_nextwp (hd win)) (Suc len') = Some (tl win)" 
      using waypoints_window_aux_success_more_than_one Suc by blast
    then have "length (tl win) = len" using Suc y2 by blast
    thus ?case using y3 y1 by auto
  qed
qed

(* We can find all next waypoint id's from a segment in its constructing waypoint list. *)
lemma waypoint_window_aux_nextwp:
"waypoints_window_aux ws i len = Some win \<Longrightarrow>
  \<forall> j < len.  (0 < j \<longrightarrow> Some (win ! j) = find_waypoint ws (get_nextwp (win ! (j - 1))))
   \<and> (j = 0 \<longrightarrow> Some (win ! j) = find_waypoint ws i)"
proof (induct len arbitrary: i win)
  case 0
  then show ?case by auto
next
  case (Suc len)
  then have "len = 0 \<or> 0 < len" by auto
  thus ?case
  proof
    assume "len = 0"
    thus ?case using Suc
      by (metis One_nat_def hd_conv_nth less_numeral_extra(3) less_one 
          waypoint_window_aux_find_waypoint_hd waypoint_window_aux_success_len_nonempty) 
  next
    assume y1:"0 < len"
    then obtain n where y2:"Suc len = Suc (Suc n)"  using gr0_conv_Suc by auto
    then have y3:"find_waypoint ws i = Some (hd win) 
      \<and> waypoints_window_aux ws (get_nextwp (hd win)) len = Some (tl win)" 
      using Suc waypoints_window_aux_success_more_than_one by blast
    then have y4:"find_waypoint ws i = Some (hd win)" and 
              y5:"waypoints_window_aux ws (get_nextwp (hd win)) len = Some (tl win)"  by auto
    then have y6:
      "\<forall>j<len. (0 < j \<longrightarrow> Some (tl win ! j) = 
          find_waypoint ws (get_nextwp (tl win ! (j - 1)))) 
       \<and> (j = 0 \<longrightarrow> Some (tl win ! j) = find_waypoint ws (get_nextwp (hd win)))" 
      using Suc(1)[OF y5] by auto
    then have y7:"\<forall>j< Suc len. (j = 0 \<longrightarrow> Some (win ! j) = find_waypoint ws i)"
      by (metis Suc.prems WaypointManager.waypoint_window_aux_success_len_nonempty 
          WaypointManager_axioms hd_conv_nth y4)
    then have y8:
      "\<forall>j<Suc len. (j = 0 \<longrightarrow> Some (win ! j) = find_waypoint ws i) 
      \<and> (j = 1 \<longrightarrow> Some (win ! j) = find_waypoint ws (get_nextwp (hd win)))" using y6 y4
      by (metis One_nat_def Suc.prems hd_Cons_tl nth_Cons_Suc 
          waypoint_window_aux_success_len_nonempty y1)
    then have 
      "\<forall>j<len. (0 < j \<longrightarrow> Some (tl win ! j) = find_waypoint ws (get_nextwp (tl win ! (j - 1))))" 
      using y6 y7 by auto
    then have "\<forall>j<len. (0 < j \<longrightarrow> Some (win ! (j + 1)) = find_waypoint ws (get_nextwp (win ! j )))"
      by (metis (no_types, hide_lams) One_nat_def Suc(2) Suc_pred' add.right_neutral add_Suc_right 
          hd_Cons_tl nth_Cons_Suc waypoint_window_aux_success_len_nonempty)
    then have 
      "\<forall>j<Suc len. (1 < j \<longrightarrow> Some (win ! j ) = find_waypoint ws (get_nextwp (win ! (j - 1) )))"
      by (metis One_nat_def Suc_lessE Suc_less_eq 
          add.right_neutral add_Suc_right diff_Suc_Suc diff_zero)
    thus ?case using y8 
      by (metis Suc_diff_1 Suc_eq_plus1_left diff_self_eq_0 linorder_neqE_nat not_add_less1 
          option.inject plus_nat.add_0 y4)
  qed
qed

(* Make the last waypoint in the segment refer to itself. *)  
fun waypoints_window :: "'w list \<Rightarrow> 'id \<Rightarrow> nat \<Rightarrow> ('w list) option" where
  "waypoints_window ws i len = 
    (case waypoints_window_aux ws i len of 
      None \<Rightarrow> None
    | Some ws \<Rightarrow> Some (butlast ws @ [ update_nextwp (last ws) (get_number (last ws)) ]))"

(* After correcting self-looping the last element the only difference in the segments is the last 
 * waypoint. *)  
lemma waypoints_window_aux_to_waypoints_window_success_rel:
"Some win' = waypoints_window_aux ws i len 
\<Longrightarrow> Some win = waypoints_window ws i len 
\<Longrightarrow> win = butlast win' @ [ update_nextwp (last win') (get_number (last win')) ]"
  apply(cases rule:waypoints_window_aux.elims) by (auto split: option.splits)
 
(* If we can get a segment we can get a self-looped segment. *)    
lemma waypoints_window_aux_to_waypoints_window_success:
"Some win' = waypoints_window_aux ws i len 
\<Longrightarrow> \<exists> win. Some win = waypoints_window ws i len 
    \<and> win = butlast win' @ [ update_nextwp (last win') (get_number (last win')) ]"
  apply(cases rule:waypoints_window_aux.elims)
     apply(auto split: option.splits)
  by metis+
   
(* The nextwp field of all but the last waypoint in a segment returned 
 * from waypoints_window_aux_is_wf can be found in the segment. *)
lemma waypoints_window_aux_is_wf:
  "Some win = waypoints_window_aux ws i len 
  \<Longrightarrow>  (\<forall> w'. List.member (butlast win) w' \<longrightarrow> (\<exists> w. Some w = find_waypoint win (get_nextwp w')))"
proof(induct len arbitrary: i win)
  case 0
  then show ?case using waypoint_window_aux_success_len_nonempty by auto
next
  case (Suc len)
  then have "len = 0 \<or> 0 < len" by auto
  thus ?case
  proof
    assume "len = 0"
    thus ?case by (metis One_nat_def Suc.prems(1) 
                   WaypointManager.waypoints_window_aux_success_length WaypointManager_axioms 
                   cancel_comm_monoid_add_class.diff_cancel 
                   length_0_conv length_butlast member_rec(2))
  next 
    assume "0 < len"
    then obtain len' where y1:"len = Suc len'"  using Suc_pred' by blast
    then have y2:"waypoints_window_aux ws i (Suc (Suc len')) = Some win" using Suc by auto
    then have y3:"find_waypoint ws i = Some (hd win) 
                  \<and> waypoints_window_aux ws (get_nextwp (hd win)) (Suc len') = Some (tl win)"
      using waypoints_window_aux_success_more_than_one y2 by auto
    then have y4:"find_waypoint ws i = Some (hd win)" 
      and y5:"waypoints_window_aux ws (get_nextwp (hd win)) (Suc len') = Some (tl win)"
      by auto
    then have y6:"Some (tl win) = waypoints_window_aux ws (get_nextwp (hd win)) len" using y1
      by auto
    then have y7:"\<forall> w'. List.member (butlast (tl win)) w' 
                  \<longrightarrow> (\<exists> w. Some w = find_waypoint (tl win) (get_nextwp w'))" 
      using Suc(1)[OF y6] by auto
    then have y8:"\<forall> w'. List.member (butlast (tl win)) w' 
                  \<longrightarrow> (\<exists> w. Some w = find_waypoint win (get_nextwp w'))" 
      by (metis Nitpick.size_list_simp(2) WaypointManager.waypoints_window_aux_success_length 
          find_waypoint_extend WaypointManager_axioms list.collapse old.nat.distinct(2) y2)
   then have y9:"Some (hd (tl win)) = find_waypoint (tl win) (get_nextwp (hd win))" 
     by (metis (mono_tags, lifting) Nitpick.size_list_simp(2) find.simps(2) find_waypoint_correct 
         find_waypoint_def list.exhaust_sel old.nat.distinct(2) 
         waypoint_window_aux_find_waypoint_hd waypoints_window_aux_success_length y1 y6)
   then have y10:"Some (hd (tl win)) = find_waypoint win (get_nextwp (hd win))"
     by (metis Suc.prems find.simps(2) find_waypoint_correct find_waypoint_def list.exhaust_sel 
         waypoint_window_aux_find_waypoint_hd waypoint_window_aux_success_len_nonempty y4 y6)
   then have y11:"\<forall> w'. List.member ((hd win)#(butlast (tl win))) w' 
                  \<longrightarrow> (\<exists> w. Some w = find_waypoint win (get_nextwp w'))"  
     by (metis y8 member_rec(1))
   then have y12:"\<forall> w'. List.member (butlast ((hd win)#(tl win))) w' 
                  \<longrightarrow> (\<exists> w. Some w = find_waypoint win (get_nextwp w'))"  
     by (simp add: member_rec(2))
   then have y13:"\<forall> w'. List.member (butlast win) w' 
                  \<longrightarrow> (\<exists> w. Some w = find_waypoint win (get_nextwp w'))" 
     by (metis find_waypoint_success_membership list.exhaust_sel member_rec(2) y10)
   thus ?case by auto
  qed
qed
  
(* A suffix can be added to find_Waypoint and not impact validity. *)  
lemma find_waypoint_success_suffix:
  "Some w = find_waypoint win i \<Longrightarrow> Some w = find_waypoint (win@winsuf) i"  
   using find_waypoint_ignores_dup_matches prefixI by blast
  
(* Modifying the last elements nextwp field preserves find_waypoint success. *)
lemma find_waypoint_success_mod_last_nextwp:
"Some w = find_waypoint win i 
  \<Longrightarrow> \<exists> w. Some w = find_waypoint ((butlast win)@[ update_nextwp (last win) x]) i"
proof(induct win arbitrary: i)
  case Nil
  then show ?case  using find_waypoint_succuss by fastforce
next
  case (Cons a win)
  then have "get_number a = i \<or> get_number a \<noteq> i" by auto
  thus ?case
  proof
    assume "get_number a = i" 
    thus ?case using find_waypoint_success_suffix Cons  by (simp add: find_waypoint_def)
  next
    assume "get_number a \<noteq> i"
    then have "Some w = find_waypoint win i" using Cons by (simp add: find_waypoint_def)
    then have "\<exists> w. Some w = find_waypoint ((butlast win)@[ update_nextwp (last win) x]) i" 
      using Cons by auto
    thus ?case using Cons find_waypoint_def by auto
  qed
qed
  
(* Membership property extension. *)    
lemma prop_on_list_prop_on_tl:
  "\<forall>w. List.member ws w \<longrightarrow> P w \<Longrightarrow>  P w' \<Longrightarrow> \<forall>w. List.member (ws@[w']) w \<longrightarrow> P w"
  apply (induct ws) by (simp add: member_rec(1))+

(* A self loop can be added safetly. *)
lemma add_self_loop_suffix: 
  assumes a1:"get_number x = get_nextwp x"
    and a2:"(\<forall> w'. List.member ws1 w' \<longrightarrow> (\<exists> w. Some w = find_waypoint (ws1@[x]) (get_nextwp w')))"
  shows 
    "(\<forall> w'. List.member (ws1@[x]) w' \<longrightarrow> (\<exists> w. Some w = find_waypoint (ws1@[x]) (get_nextwp w')))"
proof -
  have y1:"\<exists> w. Some w = find_waypoint (ws1@[x]) (get_nextwp x)"
  proof (induct ws1)
    case Nil
    then show ?case by (simp add: a1 find_waypoint_def)
  next
    case (Cons a ws1)
    then have "get_number a = (get_nextwp x) \<or> get_number a \<noteq> (get_nextwp x)" by auto
    thus ?case
    proof
      assume "get_number a = (get_nextwp x)"
      thus ?case by (simp add: find_waypoint_def)
    next
      assume "get_number a \<noteq> (get_nextwp x)"
      thus ?case by (metis (mono_tags, lifting) Cons append_Cons find_waypoint_extend)
    qed
  qed
  thus ?thesis using prop_on_list_prop_on_tl[OF a2 y1] by blast
qed
    
(* A successful call to waypoint_window returns a well-formed waypoint segment. *)
lemma waypoints_window_is_wf: "Some win = waypoints_window ws i len \<Longrightarrow>  waypoints_wf win"
proof -
  assume a1:"Some win = waypoints_window ws i len"
  then obtain win' where y1:"Some win' = waypoints_window_aux ws i len" 
    using option.splits 
    by (metis (no_types, lifting) not_Some_eq option.simps(4) waypoints_window.simps)
  then have y2:"butlast win' @ [ update_nextwp (last win') (get_number (last win')) ] = win" 
    using a1 waypoints_window_aux_to_waypoints_window_success_rel by blast
  then have y3:"(\<forall> w'. List.member (butlast win') w' 
                \<longrightarrow> (\<exists> w. Some w = 
                        find_waypoint 
                          (butlast win' @ [ update_nextwp (last win') (get_number (last win')) ]) 
                          (get_nextwp w')))" 
    using waypoints_window_aux_is_wf y1 find_waypoint_success_mod_last_nextwp by blast
  then have y4:
    "(\<forall> w'. List.member 
              (butlast win' @ [ update_nextwp (last win') (get_number (last win')) ]) 
              w' 
    \<longrightarrow> (\<exists> w. Some w = 
                find_waypoint 
                  (butlast win' @ [ update_nextwp (last win') (get_number (last win')) ]) 
                  (get_nextwp w')))" 
    using add_self_loop_suffix[OF _ y3] by auto
  thus ?thesis using y2 waypoints_wf_def by auto
qed
end
  
end