theory WaypointManagerFunSpec imports 
Main
Sublist
"~~/src/HOL/Library/Multiset"
begin
(* TODO:
   refactor specification to use multisets instead of lists. 
*)
  
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
    
lemma find_waypoint_success_mset_membership:"Some w = find_waypoint ws i \<Longrightarrow> (get_number w) \<in># mset (map get_number ws)"
  apply(induct ws arbitrary: i w)
    apply (auto simp add: find_waypoint_def)
     by (metis find_Some_iff option.inject)

lemma find_waypoint_success_set_membership:"Some w = find_waypoint ws i \<Longrightarrow> (get_number w) \<in> set (map get_number ws)"
  apply(induct ws arbitrary: i w)
    apply (auto simp add: find_waypoint_def)
     by (metis find_Some_iff option.inject)

lemma find_waypoint_correct:"find_waypoint ws i = Some w \<Longrightarrow> get_number w = i"
  apply(induct ws)
   apply (simp add: find_waypoint_def)
  by (metis find_waypoint_success_id)
    
lemma find_waypoint_extend:"find_waypoint ws i = Some w \<Longrightarrow> \<exists> w'. find_waypoint (a#ws) i = Some w'"
  by (simp add: find_waypoint_def)
    
definition waypoints_wf where
  "waypoints_wf ws \<equiv> 
  (\<forall> w'. List.member ws w' \<longrightarrow> (\<exists> w. Some w = find_waypoint ws (get_nextwp w'))) 
  \<and> (\<forall> w'. List.member (tl ws) w' \<longrightarrow>  (\<exists> w w''. Some w'' = find_waypoint ws (get_nextwp w) \<and> get_number w = get_number w''))"
     
(* Some odd behavior:
  - By definition of this function, cycles in the incoming 'w list will be unrolled in the output
    window. This means that there may be multiple waypoints in the same window with the same number.
    Thus we cannot demand wellformed windows have the property:
      (\<forall> w'. List.member (tl ws) w' \<longrightarrow>  (\<exists> w. Some w' = find_waypoint ws (get_nextwp w)))
*)
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
          (case waypoints_window ws (get_nextwp w) (Suc n) of
            None \<Rightarrow> None
            | Some win \<Rightarrow> Some (w # win)))"

lemma waypoints_window_elim1:"waypoints_window ws i 0 = x \<Longrightarrow> x = None"
  apply(cases rule:waypoints_window.cases) by auto
    
lemma waypoints_window_elim2:
  "waypoints_window ws i (Suc 0) = x \<Longrightarrow> find_waypoint ws i = Some w \<Longrightarrow> x = Some [update_nextwp w i]"
apply(cases rule:waypoints_window.elims) by auto 

lemma waypoints_window_elim3: "waypoints_window ws i n = x \<Longrightarrow> find_waypoint ws i = None \<Longrightarrow> x = None"
  apply(cases rule:waypoints_window.elims) by auto
        
lemma waypoints_window_elim5: "waypoints_window ws i (Suc (Suc n)) = x \<Longrightarrow> find_waypoint ws i = Some w  \<Longrightarrow> waypoints_window ws (get_nextwp w) (Suc n) = None \<Longrightarrow> x = None"
  apply(cases rule:waypoints_window.elims) by auto
    
lemma waypoints_window_elim6: "waypoints_window ws i (Suc (Suc n)) = x \<Longrightarrow> find_waypoint ws i = Some w  \<Longrightarrow> waypoints_window ws (get_nextwp w) (Suc n) = Some win \<Longrightarrow> x = Some (w # win)"
  apply(cases rule:waypoints_window.elims) by auto
    
lemma waypoints_window_elim7:
  "waypoints_window ws i (Suc 0) = Some win \<Longrightarrow> \<exists> w. find_waypoint ws i = Some w \<and> win = [update_nextwp w i]"
  apply(cases rule:waypoints_window.cases,auto) by (metis (no_types, lifting) option.case_eq_if option.collapse option.inject option.simps(3))

lemma waypoints_window_elim8:assumes assm:"waypoints_window ws i n = Some win"
  shows "\<exists> w. find_waypoint ws i = Some w \<and> (hd win = w \<or> hd win = update_nextwp w i)"
  apply(cases rule:waypoints_window.elims[OF assm])
  by (auto split:option.splits)
    
lemma waypoints_window_elim9:
assumes assm1:"waypoints_window ws i (Suc (Suc n)) = Some win"
and assm2:"find_waypoint ws i = Some w"
shows "\<exists> win' . waypoints_window ws (get_nextwp w) (Suc n) = Some win' \<and> win = w # win'"
apply(cases rule:waypoints_window.elims[OF assm1])
using assm2  by (auto split: option.splits)

lemma waypoints_window_elim10:
  assumes assm1:"waypoints_window ws i (Suc (Suc n)) = Some win"
  shows "(\<exists> w. find_waypoint ws i = Some w \<and> (win = [w] \<or> (\<exists> win'. win = w # win')))"
  apply(cases rule:waypoints_window.elims[OF assm1])
    by (auto split:option.splits)

lemma waypoints_window_intro1:"waypoints_window ws i 0 = None"
  apply(cases rule:waypoints_window.elims) by auto
 
lemma waypoints_window_intro2: "find_waypoint ws i = Some w \<Longrightarrow> waypoints_window ws i (Suc 0) = Some [update_nextwp w i]"
apply(cases rule:waypoints_window.elims) by auto 

lemma waypoints_window_intro3: "find_waypoint ws i = None \<Longrightarrow> waypoints_window ws i n = None"
  apply(cases rule:waypoints_window.elims) by auto

lemma waypoints_window_intro5: "find_waypoint ws i = Some w \<Longrightarrow>  waypoints_window ws (get_nextwp w) (Suc n) = None \<Longrightarrow> waypoints_window ws i (Suc (Suc n)) = None"
  apply(cases rule:waypoints_window.elims) by auto

lemma waypoints_window_intro6: "find_waypoint ws i = Some w \<Longrightarrow> waypoints_window ws (get_nextwp w) (Suc n) = Some win \<Longrightarrow> waypoints_window ws i (Suc (Suc n)) = Some (w # win)"
  apply(cases rule:waypoints_window.elims) by auto    

lemma waypoints_window_intro8:"Some w = find_waypoint ws i \<Longrightarrow> waypoints_window ws i (Suc 0) = Some [update_nextwp w i]"
  using waypoints_window_intro2 by presburger

lemma waypoints_window_success_find_waypoint_success:"waypoints_window ws i (Suc n) = Some ws \<Longrightarrow> \<exists> w. find_waypoint ws i = Some w"
  using waypoints_window_intro3 by fastforce
  
lemma waypoints_window_size_one_success_is_size_one:
  "waypoints_window ws i (Suc 0) = Some win \<Longrightarrow> length win = (Suc 0)" using waypoints_window_elim7 by force

    
lemma waypoints_window_lteq_len:"waypoints_window ws i len = Some win \<Longrightarrow> length win = len"
  apply(induct arbitrary: win rule:waypoints_window.induct)  
    by (auto split: option.splits)
  
lemma waypoints_window_output_forms:"waypoints_window ws i len = None \<or> (\<exists> w win. waypoints_window ws i len = Some (w # win))"
  apply(cases rule:waypoints_window.induct) by (auto simp add: option.case_eq_if)
  
lemma waypoints_window_not_empty:"waypoints_window ws i len = Some [] \<Longrightarrow> False"
  by (metis list.distinct(1) not_None_eq option.inject waypoints_window_output_forms)
    
lemma waypoints_window_length_one_head_end_or_not:"waypoints_window ws i (Suc n) = Some win \<Longrightarrow> get_nextwp (hd win) = i \<or> get_nextwp (hd win) \<noteq> i"    
  apply(cases rule:waypoints_window.cases) by auto
     
lemma waypoints_window_length_one: "waypoints_window ws i (Suc 0) = Some win \<Longrightarrow> (\<exists> w. win = w # [] \<and> get_nextwp w = get_number w)"
  apply (cases rule:waypoints_window.cases)
    apply (auto split: option.splits)
  by (metis find_waypoint_success_id)
    
lemma waypoints_window_last_is_cycle:"waypoints_window ws i len = Some win \<Longrightarrow> get_number (last win) = x \<Longrightarrow> get_nextwp (last win) = x"
  apply(induct arbitrary: win x rule:waypoints_window.induct)
    apply (auto split:option.splits)
    by (metis find_waypoint_succuss find_waypoint_correct last_ConsL option.inject last.simps option.sel waypoints_window_not_empty)+
    
lemma waypoint_wf_update_singleton:"waypoints_wf [update_nextwp w (get_number w)]"
  apply(unfold waypoints_wf_def)
  apply (auto simp add: member_rec(2) )
    by (metis append_Nil correct_update1 correct_update2 find.simps(1) find_waypoint_def find_waypoint_none_extend_some member_rec(1) member_rec(2))
  
lemma shrink_submultiset:"Multiset.mset (x # xs) \<subseteq># mset ys \<Longrightarrow> Multiset.mset xs \<subseteq># mset ys"   
  apply(induct xs)
    apply auto
  by (metis mset_subset_eq_exists_conv union_mset_add_mset_left union_mset_add_mset_right)
  
lemma grow_submultiset:"Multiset.mset xs \<subseteq># mset ys \<Longrightarrow> x \<notin># mset xs \<Longrightarrow> x \<in># mset ys \<Longrightarrow> mset (x # xs) \<subseteq># mset ys"   
proof(induct xs arbitrary: ys)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  then obtain ys' where y1:"mset ys = add_mset a (mset ys')"  by (metis ex_mset mset.simps(2) mset_add mset_subset_eq_insertD)
  then have y2:"mset xs \<subseteq># mset ys'" using shrink_submultiset using Cons by auto
  then have y3:"x \<notin># mset xs" using Cons by auto
  then have y4:"a \<in># mset ys" using Cons by (simp add: insert_subset_eq_iff)
  then have y5:"mset (x # xs) \<subseteq># mset ys'" using Cons y1 y2 y3 by auto
  thus ?case using Cons y5 y1 by auto 
qed

lemma mset_extend_submultiset:"x \<notin># Multiset.mset xs' \<Longrightarrow> x \<in># mset xs \<Longrightarrow> mset xs' \<subseteq># mset xs \<Longrightarrow> mset (x# xs') \<subseteq># mset xs"
  proof(induct xs')
    case Nil
    then show ?case by auto
  next
    case (Cons a xs')
    then have y1:"x \<notin># mset xs'" by auto
    then have y2:"mset xs' \<subseteq># mset xs" using Cons shrink_submultiset by auto
    then show ?case using Cons y1 y2 by (meson grow_submultiset)
  qed    
     
      
lemma waypoints_window_wf:"waypoints_window ws i len = Some win \<Longrightarrow> waypoints_wf win"
proof(induct arbitrary: win rule:waypoints_window.induct)
  case (1 ws i)
  then show ?case by auto
next
  case (2 ws i)
  then show ?case by (metis correct_update3 waypoint_wf_update_singleton waypoints_window_length_one)
next
  case (3 ws i n)
  then obtain w where y1:"find_waypoint ws i = Some w" by fastforce
  then obtain win' where y2:"waypoints_window ws (get_nextwp w) (Suc n) = Some win'" and y3:"win = w # win'"  using 3 waypoints_window_elim9 y1 by blast
  then have y4:"waypoints_wf win'" using 3 y1 by blast
  then have y5:"\<forall> w'. List.member win' w' \<longrightarrow> (\<exists> w. Some w = find_waypoint win' (get_nextwp w'))" 
      and y6:"\<forall> w'. List.member (tl win') w' \<longrightarrow>  (\<exists> w w''. Some w'' = find_waypoint win' (get_nextwp w) \<and> get_number w = get_number w'')"
      using waypoints_wf_def by auto
  then have y7:"get_nextwp w = get_number (hd win')"  using find_waypoint_correct waypoints_window_elim8 y2 by fastforce
  then have y8:"\<forall> w'. List.member win w' \<longrightarrow> (\<exists> w''. Some w'' = find_waypoint win (get_nextwp w'))" 
    by (metis (mono_tags, lifting) WaypointManager.waypoints_wf_def WaypointManager.waypoints_window_not_empty y3 WaypointManager_axioms find.simps(2) find_waypoint_def list.collapse member_rec(1) y2 y4)
  then have y9:"\<forall> w'. List.member (tl win) w' \<longrightarrow>  (\<exists> w' w''. Some w'' = find_waypoint win (get_nextwp w') \<and> get_number w = get_number w'')"
    by (metis (mono_tags, lifting) correct_update1 correct_update2 find.simps(2) find_waypoint_def y3)
  thus ?case using y8 y9 waypoints_wf_def[of win] by (metis correct_update1 correct_update2)
qed

lemma waypoints_window_sensible_numbers:"waypoints_window ws i len = Some win \<Longrightarrow> set (map get_number win) \<subseteq> set (map get_number ws)"
proof(induct arbitrary: win rule:waypoints_window.induct)
  case (1 ws i)
  thus ?case by auto
next
  case (2 ws i)
  then obtain w where y1:"find_waypoint ws i = Some w" and y2:"win = [update_nextwp w i]" using waypoints_window_elim7 by blast
  then have "get_number w \<in> set (map get_number ws)"
    by (metis find_waypoint_success_set_membership)
  then have "get_number (update_nextwp w i) \<in> set (map get_number ws)" by auto
  thus ?case using y2 by auto
next
  case (3 ws i n)
  then obtain w where y1:"find_waypoint ws i = Some w" by fastforce
  then have y2:"get_number w \<in> set (map get_number ws)" by (metis y1 find_waypoint_success_set_membership)
  then have y3:"get_number (update_nextwp w i) \<in> set (map get_number ws)" by auto
  then have "get_nextwp w = i \<or> get_nextwp w \<noteq> i" by auto
  then obtain win' where y4:"waypoints_window ws (get_nextwp w) (Suc n) = Some win'" and y5:"win = w # win'"  using 3 waypoints_window_elim9 y1 by blast
  then have y6:" set (map get_number win') \<subseteq> set (map get_number ws)" using 3 y1 by auto
  thus ?case using y3 y5 by auto
qed
  
  
end
  
end