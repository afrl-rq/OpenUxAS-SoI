theory WaypointManagerFunSpec imports 
Main
Sublist
begin
  
locale WaypointManager =
  fixes get_number :: "'w \<Rightarrow> 'id"
  fixes get_nextwp :: "'w \<Rightarrow> 'id"
  fixes update_nextwp :: "'w \<Rightarrow> 'id \<Rightarrow> 'w"
  assumes correct_update1[simp,intro]:"get_nextwp (update_nextwp w i) = i"
  assumes correct_update2[simp,intro]:"get_number (update_nextwp w i) = get_number w"
  assumes correct_update3[simp,intro]:"get_nextwp w = i \<Longrightarrow> w = update_nextwp w i"
    
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
lemma find_waypoint_succuss:"Some w = find_waypoint ws i \<Longrightarrow> \<exists> j. j < length ws \<and> w = ws ! j \<and> i = get_number w"
  apply(induct ws)
   apply (simp add: find_waypoint_def)
    by (metis (mono_tags, lifting) find_Some_iff find_waypoint_def)    

(* Ditto *)
lemma find_waypoint_failure_not_equal_all_elems:"None = find_waypoint ws n \<Longrightarrow> \<forall> i < length ws. get_number (ws ! i) \<noteq> n"
proof(induct ws)
  case Nil
  then show ?case by auto
next
  case (Cons a ws)
  then have "None = find_waypoint ws n \<and> get_number a \<noteq> n"
    by (metis (mono_tags) find_waypoint_def find.simps(2) option.distinct(1))
  then show ?case using Cons by (metis Suc_less_eq gr0_conv_Suc length_Cons not_gr_zero nth_Cons_0 nth_Cons_Suc)
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

(* TODO: Tricky one to summarize nicely off the top of my head. *) 
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
lemma find_waypoint_success_construction:"Some w = find_waypoint ws i \<Longrightarrow> (\<exists> ws' ws''. ws'@ w # ws'' = ws \<and> None = find_waypoint ws' i)"
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
lemma find_waypoint_disaggree_absurd:"None = find_waypoint ws i \<Longrightarrow> Some w = find_waypoint ws i \<Longrightarrow> False" by auto  
  
(* Whatever find_waypoints finds is in the list. *)
lemma find_waypoint_success_membership:"Some w = find_waypoint ws i \<Longrightarrow> List.member ws w"
  using WaypointManager.find_waypoint_success_construction in_set_member WaypointManager_axioms by fastforce

lemma find_waypoint_correct:"find_waypoint ws i = Some w \<Longrightarrow> get_number w = i"
  apply(induct ws)
   apply (simp add: find_waypoint_def)
   by (metis find_waypoint_success_id)
        
definition waypoints_wf where
  "waypoints_wf ws \<equiv> 
  (\<forall> w'. List.member ws w' \<longrightarrow> (\<exists> w. Some w = find_waypoint ws (get_nextwp w'))) 
  \<and> (\<forall> w'. List.member (tl ws) w' \<longrightarrow>  (\<exists> w. Some w' = find_waypoint ws (get_nextwp w)))"
    
fun waypoints_window :: "'w list \<Rightarrow> 'id \<Rightarrow> nat \<Rightarrow> ('w list) option" where
case1:"waypoints_window ws i 0 = None"
|case2:"waypoints_window ws i (Suc 0) = 
  (case find_waypoint ws i of 
    None \<Rightarrow> None 
    | Some w \<Rightarrow> Some [update_nextwp w i])"
|case3:"waypoints_window ws i (Suc (Suc n)) = 
  (case find_waypoint ws i of 
    None \<Rightarrow> None 
    | Some w \<Rightarrow> 
      (if get_nextwp w = i 
        then Some [w]
        else 
          (case waypoints_window ws (get_nextwp w) (Suc n) of
            None \<Rightarrow> None
            | Some win \<Rightarrow> Some (w # win))))"

lemma waypoints_window_elim1:"waypoints_window ws i 0 = x \<Longrightarrow> x = None"
  apply(cases rule:waypoints_window.cases) by auto
    
lemma waypoints_window_elim2:
  "waypoints_window ws i (Suc 0) = x \<Longrightarrow> find_waypoint ws i = Some w \<Longrightarrow> x = Some [update_nextwp w i]"
apply(cases rule:waypoints_window.elims) by auto 

lemma waypoints_window_elim3: "waypoints_window ws i n = x \<Longrightarrow> find_waypoint ws i = None \<Longrightarrow> x = None"
  apply(cases rule:waypoints_window.elims) by auto
    
lemma waypoints_window_elim4: "waypoints_window ws i (Suc (Suc n)) = x \<Longrightarrow> find_waypoint ws i = Some w \<Longrightarrow> get_nextwp w = i \<Longrightarrow> x = Some [update_nextwp w i]"
  apply(cases rule:waypoints_window.elims) by auto
    
lemma waypoints_window_elim5: "waypoints_window ws i (Suc (Suc n)) = x \<Longrightarrow> find_waypoint ws i = Some w \<Longrightarrow> get_nextwp w \<noteq> i \<Longrightarrow> waypoints_window ws (get_nextwp w) (Suc n) = None \<Longrightarrow> x = None"
  apply(cases rule:waypoints_window.elims) by auto
    
lemma waypoints_window_elim6: "waypoints_window ws i (Suc (Suc n)) = x \<Longrightarrow> find_waypoint ws i = Some w \<Longrightarrow> get_nextwp w \<noteq> i \<Longrightarrow> waypoints_window ws (get_nextwp w) (Suc n) = Some win \<Longrightarrow> x = Some (w # win)"
  apply(cases rule:waypoints_window.elims) by auto
    
lemma waypoints_window_elim7:
  "waypoints_window ws i (Suc 0) = Some win \<Longrightarrow> \<exists> w. find_waypoint ws i = Some w \<and> win = [update_nextwp w i]"
  apply(cases rule:waypoints_window.cases,auto) by (metis (no_types, lifting) option.case_eq_if option.collapse option.inject option.simps(3))

lemma waypoints_window_intro1:"waypoints_window ws i 0 = None"
  apply(cases rule:waypoints_window.elims) by auto
 
lemma waypoints_window_intro2: "find_waypoint ws i = Some w \<Longrightarrow> waypoints_window ws i (Suc 0) = Some [update_nextwp w i]"
apply(cases rule:waypoints_window.elims) by auto 

lemma waypoints_window_intro3: "find_waypoint ws i = None \<Longrightarrow> waypoints_window ws i n = None"
  apply(cases rule:waypoints_window.elims) by auto

lemma waypoints_window_intro4: "find_waypoint ws i = Some w \<Longrightarrow> get_nextwp w = i \<Longrightarrow> waypoints_window ws i (Suc (Suc n)) = Some [update_nextwp w i]"
  apply(cases rule:waypoints_window.elims) by auto

lemma waypoints_window_intro5: "find_waypoint ws i = Some w \<Longrightarrow> get_nextwp w \<noteq> i \<Longrightarrow> waypoints_window ws (get_nextwp w) (Suc n) = None \<Longrightarrow> waypoints_window ws i (Suc (Suc n)) = None"
  apply(cases rule:waypoints_window.elims) by auto

lemma waypoints_window_intro6: "find_waypoint ws i = Some w \<Longrightarrow> get_nextwp w \<noteq> i \<Longrightarrow> waypoints_window ws (get_nextwp w) (Suc n) = Some win \<Longrightarrow> waypoints_window ws i (Suc (Suc n)) = Some (w # win)"
  apply(cases rule:waypoints_window.elims) by auto    
 
lemma waypoints_window_intro7:"Some w = find_waypoint ws i \<Longrightarrow> get_nextwp w = i \<Longrightarrow> waypoints_window ws i (Suc 0) = Some [w]"
  by (metis correct_update3 waypoints_window_intro2)

lemma waypoints_window_intro8:"Some w = find_waypoint ws i \<Longrightarrow> get_nextwp w \<noteq> i \<Longrightarrow> waypoints_window ws i (Suc 0) = Some [update_nextwp w i]"
  using waypoints_window_intro2 by presburger

lemma waypoints_window_success_find_waypoint_success:"waypoints_window ws i (Suc n) = Some ws \<Longrightarrow> \<exists> w. find_waypoint ws i = Some w"
  using waypoints_window_intro3 by fastforce
  
lemma waypoints_window_size_one_success_is_size_one:
  "waypoints_window ws i (Suc 0) = Some win \<Longrightarrow> length win = (Suc 0)" using waypoints_window_elim7 by force
    
    
lemma case_rewrite[simp]:"(Some x = (case f of None \<Rightarrow> None | Some y \<Rightarrow> g y)) = (\<exists> y. Some x = g y \<and> f = Some y)"
proof
  assume "Some x = (case f of None \<Rightarrow> None | Some y \<Rightarrow> g y)"
  thus "\<exists>y. Some x = g y \<and> f = Some y" by (metis option.case_eq_if option.exhaust_sel option.simps(3))
next
  assume "\<exists>y. Some x = g y \<and> f = Some y"
  thus "Some x = (case f of None \<Rightarrow> None | Some y \<Rightarrow> g y)" by auto
qed
    
lemma waypoints_window_lteq_len:"waypoints_window ws i len = Some win \<Longrightarrow> length win \<le> len"
  apply(induct arbitrary: win rule:waypoints_window.induct)  
    apply(auto split: option.splits)
   by (metis One_nat_def Suc_eq_plus1_left le_add_same_cancel1 less_Suc_eq_le option.simps(3) waypoints_window_intro7 waypoints_window_size_one_success_is_size_one zero_less_Suc eq_iff le0 le_Suc_eq length_Cons list.size(3) nat_le_linear option.sel)+
  
lemma waypoints_window_output_forms:"waypoints_window ws i len = None \<or> (\<exists> w win. waypoints_window ws i len = Some (w # win))"
  apply(cases rule:waypoints_window.induct) by (auto simp add: option.case_eq_if)
  
lemma waypoints_window_not_empty:"waypoints_window ws i len = Some [] \<Longrightarrow> False"
  by (metis list.distinct(1) not_None_eq option.inject waypoints_window_output_forms)
    
lemma waypoints_window_length_one_head_end_or_not:"waypoints_window ws i (Suc n) = Some win \<Longrightarrow> get_nextwp (hd win) = i \<or> get_nextwp (hd win) \<noteq> i"    
  apply(cases rule:waypoints_window.cases) by auto
 
thm waypoints_window.elims    
    
lemma waypoints_window_success_self_reference: "waypoints_window ws i (Suc n) = Some win \<Longrightarrow> get_nextwp (hd win) = i \<Longrightarrow> length win = 1"
  apply(cases n)
    apply (auto split:option.splits)
    by (metis option.simps(3) waypoints_window_intro7 waypoints_window_size_one_success_is_size_one length_Cons list.sel(1) list.size(3) option.sel)+
    
lemma waypoints_window_length_one: "waypoints_window ws i (Suc 0) = Some win \<Longrightarrow> (\<exists> w. win = w # [] \<and> get_nextwp w = get_number w)"
  apply (cases rule:waypoints_window.cases)
    apply (auto split: option.splits)
  by (metis find_waypoint_success_id)
    
lemma waypoints_window_last_is_cycle:"waypoints_window ws i len = Some win \<Longrightarrow> get_number (last win) = x \<Longrightarrow> get_nextwp (last win) = x"
  apply(induct arbitrary: win x rule:waypoints_window.induct)
    apply (auto split:option.splits)
    by (metis find_waypoint_succuss find_waypoint_correct last_ConsL option.inject last.simps option.sel waypoints_window_not_empty)+
(*  
lemma waypoints_window_succes_first_two:" waypoints_window ws i len = Some win \<Longrightarrow> get_nextwp (hd win) = get_number (hd win) \<or> get_nextwp (hd win) = get_number (hd (tl win))" 
  apply(cases len)
   apply auto
    sledgehammer[z3 e spass]
  
  proof(induct arbitrary: win rule:waypoints_window.induct)
    case (1 ws i)
    then show ?case by auto
  next
    case (2 ws i)
    then obtain w where y1:"find_waypoint ws i = Some w" by fastforce
    thus ?case by (metis 2 append_Nil hd_Cons_tl last_snoc length_0_conv length_Suc_conv list.sel waypoints_window_last_is_cycle waypoints_window_size_one_success_is_size_one)
  next
    case (3 ws i n)
    then obtain w where y1:"find_waypoint ws i = Some w" by fastforce
    then have y2:"get_nextwp w = i \<or> get_nextwp w \<noteq> i" by auto
    thus ?case
    proof
      assume "get_nextwp w = i"
      thus ?case using 3 y1 by (metis (mono_tags) find.simps find_waypoint_correct1 find_waypoint_def list.sel member_rec option.sel waypoints_wf_def waypoints_window_simp3)
    next
      assume a:"get_nextwp w \<noteq> i"
      then obtain win' where y3:"waypoints_window ws (get_nextwp w) (Suc n) = Some win'" and y4:"win = w # win'" using waypoints_window_size_at_least_two_success_elim 3 y1 by blast
      then have "find_waypoint ws (get_nextwp w) = Some w" 
 sledgehammer[z3 e spass]
(*      then show ?case using 3(1)[OF y1 a y3] *)
  qed
*)
    
lemma waypoint_wf_update_singleton:"waypoints_wf [update_nextwp w (get_number w)]"
  by (simp add: find_waypoint_def member_rec waypoints_wf_def)

lemma foo:"((if get_nextwp w = i then Some [w] else Some (w # ws)) = Some win) = ((Some [w] = Some win \<and> get_nextwp w = i) \<or> (Some (w # ws) = Some win \<and> get_nextwp w \<noteq> i))"  
sorry

lemma waypoints_window_wf:" waypoints_window ws i len = Some win \<Longrightarrow> waypoints_wf win"
proof(induct arbitrary: win rule:waypoints_window.induct)
  case (1 ws i)
  then show ?case by auto
next
  case (2 ws i)
  then show ?case by (metis correct_update3 waypoint_wf_update_singleton waypoints_window_length_one)
next
  case (3 ws i n)
  then obtain w where y1:"find_waypoint ws i = Some w" by fastforce
  then have "get_nextwp w = i \<or> get_nextwp w \<noteq> i" by auto
  thus ?case
  proof
    assume a:"get_nextwp w = i"
    then have "win = [w]" using 3 y1 by force
    thus ?thesis by (metis a correct_update3 find_waypoint_correct waypoint_wf_update_singleton y1)
  next
    assume a:"get_nextwp w \<noteq> i"
    then obtain win' where y2:"waypoints_window ws (get_nextwp w) (Suc n) = Some win'" and y3:"win = w # win'" sorry
    then have "waypoints_wf win'" using 3 y1 a by blast
    then have "find_waypoint ws (get_nextwp w) = Some (hd win')" sledgehammer[z3 e spass]
qed
  

(*  
proof(induct arbitrary: win rule:waypoints_window.induct)
  case (1 ws i)
  then show ?case by auto
next
  case (2 ws i)
  then obtain w where y1:"find_waypoint ws i = Some w" by fastforce
  then have y2:"get_nextwp w = i \<or> get_nextwp w \<noteq> i" by auto
  thus ?case
  proof
    assume a:"get_nextwp w = i"
    then have "win= [w]" using 2 y1 by auto 
    thus ?case by (metis "2.prems" append_Nil find.simps find_waypoint_def find_waypoint_none_extend_some last.simps list.sel member_rec waypoints_wf_def waypoints_window_last_is_cycle)
  next
    assume "get_nextwp w \<noteq> i"
    then have y2:"win = [update_nextwp w i]" using 2 y1 by auto
     thus ?case by (metis 2 append_Nil find.simps(1) find_waypoint_def find_waypoint_none_extend_some last.simps list.sel member_rec waypoints_wf_def waypoints_window_last_is_cycle)   
  qed
next
  case (3 ws i n)
  then obtain w where y1:"find_waypoint ws i = Some w" by fastforce
  then have y2:"get_nextwp w = i \<or> get_nextwp w \<noteq> i" by auto
  thus ?case
  proof
    assume "get_nextwp w = i"
    thus ?case using 3 y1 by (metis (mono_tags) find.simps find_waypoint_correct1 find_waypoint_def list.sel member_rec option.sel waypoints_wf_def waypoints_window_simp3)
  next
    assume a:"get_nextwp w \<noteq> i"
    then obtain win' where y3:"waypoints_window ws (get_nextwp w) (Suc n) = Some win'" and y4:"win = w # win'" using waypoints_window_size_at_least_two_success_elim 3 y1 by blast
    then obtain w' win'' where y5:"win' = w' # win''"using y1 3 a by (metis neq_Nil_conv waypoints_window_not_empty)
    then have y6:"find_waypoint ws (get_nextwp w) = Some w'"(* sledgehammer[z3 e spass]*)
(*    then have "get_nextwp w = get_number(hd win')" sledgehammer[z3 e spass] *)
(*    thus ?case using 3(1)[OF y1 a y3] a y1 sledgehammer[z3 e spass] *)
  qed *)
qed
    
end
  
end