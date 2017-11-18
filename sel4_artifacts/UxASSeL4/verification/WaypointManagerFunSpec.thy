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
  (*\<and> (\<forall> w'. List.member (tl ws) w' \<longrightarrow>  (\<exists> w w''. List.member ws w 
         \<and> Some w'' = find_waypoint ws (get_nextwp w) 
         \<and> get_number w' = get_number w''))*)"
  
lemma waypoints_wf_result:"waypoints_wf ws \<Longrightarrow> List.member ws w' \<Longrightarrow> (\<exists> w. Some w = find_waypoint ws (get_nextwp w'))"
  using waypoints_wf_def by auto
     
(* Some odd behavior:
  - By definition of this function, cycles in the incoming 'w list will be unrolled in the output
    window. This means that there may be multiple waypoints in the same window with the same number.
    Thus we cannot demand wellformed windows have the property:
      (\<forall> w'. List.member (tl ws) w' \<longrightarrow>  (\<exists> w. Some w' = find_waypoint ws (get_nextwp w)))
*)
  
  
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

lemma waypoint_window_aux_find_waypoint_hd:"waypoints_window_aux ws i len = Some win \<Longrightarrow> Some (hd (win)) = find_waypoint ws i"
  apply (induct rule:waypoints_window_aux.induct)
    by (auto split: option.splits)

lemma  waypoint_window_aux_success_len_nonzero:"waypoints_window_aux ws i len = Some win \<Longrightarrow> 0 < len"
  apply (induct len)
  by (auto split: option.splits)
    
lemma waypoint_window_aux_success_len_nonempty: assumes a:"waypoints_window_aux ws i len = Some []" shows " False"
  apply(cases rule:waypoints_window_aux.elims[OF a])
  by (auto split: option.splits)
    
lemma waypoints_window_aux_success_more_than_one:
  "waypoints_window_aux ws i (Suc (Suc n)) = Some win \<Longrightarrow> find_waypoint ws i = Some (hd win) \<and> waypoints_window_aux ws (get_nextwp (hd win)) (Suc n) = Some (tl win)"
  apply(cases rule:waypoints_window_aux.elims)
  by (auto split:option.splits)
    
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
      by (metis One_nat_def hd_conv_nth less_numeral_extra(3) less_one waypoint_window_aux_find_waypoint_hd waypoint_window_aux_success_len_nonempty) 
  next
    assume y1:"0 < len"
    then obtain n where y2:"Suc len = Suc (Suc n)"  using gr0_conv_Suc by auto
    then have y3:"find_waypoint ws i = Some (hd win) \<and> waypoints_window_aux ws (get_nextwp (hd win)) len = Some (tl win)" 
      using Suc waypoints_window_aux_success_more_than_one by blast
    then have y4:"find_waypoint ws i = Some (hd win)" and y5:"waypoints_window_aux ws (get_nextwp (hd win)) len = Some (tl win)"  by auto
    then have y6:" \<forall>j<len. (0 < j \<longrightarrow> Some (tl win ! j) = find_waypoint ws (get_nextwp (tl win ! (j - 1)))) \<and> (j = 0 \<longrightarrow> Some (tl win ! j) = find_waypoint ws (get_nextwp (hd win)))" using Suc(1)[OF y5] by auto
    then have y7:"\<forall>j< Suc len. (j = 0 \<longrightarrow> Some (win ! j) = find_waypoint ws i)"
      by (metis Suc.prems WaypointManager.waypoint_window_aux_success_len_nonempty WaypointManager_axioms hd_conv_nth y4)
    then have y8:"\<forall>j<Suc len. (j = 0 \<longrightarrow> Some (win ! j) = find_waypoint ws i) \<and> (j = 1 \<longrightarrow> Some (win ! j) = find_waypoint ws (get_nextwp (hd win)))" using y6 y4
      by (metis One_nat_def Suc.prems hd_Cons_tl nth_Cons_Suc waypoint_window_aux_success_len_nonempty y1)
    then have "\<forall>j<len. (0 < j \<longrightarrow> Some (tl win ! j) = find_waypoint ws (get_nextwp (tl win ! (j - 1))))" using y6 y7 by auto
    then have "\<forall>j<len. (0 < j \<longrightarrow> Some (win ! (j + 1)) = find_waypoint ws (get_nextwp (win ! j )))"
      by (metis (no_types, hide_lams) One_nat_def Suc(2) Suc_pred' add.right_neutral add_Suc_right hd_Cons_tl nth_Cons_Suc waypoint_window_aux_success_len_nonempty)
    then have "\<forall>j<Suc len. (1 < j \<longrightarrow> Some (win ! j ) = find_waypoint ws (get_nextwp (win ! (j - 1) )))"
      by (metis One_nat_def Suc_lessE Suc_less_eq add.right_neutral add_Suc_right diff_Suc_Suc diff_zero)
    thus ?case using y8 
      by (metis Suc_diff_1 Suc_eq_plus1_left diff_self_eq_0 linorder_neqE_nat not_add_less1 option.inject plus_nat.add_0 y4)
  qed
qed
  

    
fun waypoints_window :: "'w list \<Rightarrow> 'id \<Rightarrow> nat \<Rightarrow> ('w list) option" where
"waypoints_window ws i 0 = None"
|"waypoints_window ws i (Suc 0) = 
  (case find_waypoint ws i of 
    None \<Rightarrow> None 
    | Some w \<Rightarrow> Some [update_nextwp w i])"
|"waypoints_window ws i (Suc (Suc n)) = 
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

lemma option_non_none:"((case option of None \<Rightarrow> None | Some x \<Rightarrow> f x) = Some g) = (\<exists> x. option = Some x \<and> f x = Some g )"
  by (auto split: option.split)
        
lemma waypoints_window_elim11:
  "waypoints_window ws i (Suc 0) = Some win \<Longrightarrow> \<exists> w. find_waypoint ws i = Some w \<and> win = [update_nextwp w i]"
  by (auto simp add: option_non_none)

lemma waypoints_window_elim12:
  "waypoints_window ws i (Suc (Suc n)) = Some win \<Longrightarrow> find_waypoint ws i = Some (hd win) \<and> waypoints_window ws (get_nextwp (hd win)) (Suc n) = Some (tl win)"
  apply(cases rule:waypoints_window.elims)
  by (auto split:option.splits)
    
lemma waypoints_window_elim12:"waypoints_window ws i len = Some win \<Longrightarrow> 1 \<le> len"
  apply(induct rule:waypoints_window.induct) by auto
    
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
      using waypoints_wf_def by auto
  then have y7:"get_nextwp w = get_number (hd win')"  using find_waypoint_correct waypoints_window_elim8 y2 by fastforce
  then have y8:"\<forall> w'. List.member win w' \<longrightarrow> (\<exists> w''. Some w'' = find_waypoint win (get_nextwp w'))" 
    by (metis (mono_tags, lifting) WaypointManager.waypoints_wf_def WaypointManager.waypoints_window_not_empty y3 WaypointManager_axioms find.simps(2) find_waypoint_def list.collapse member_rec(1) y2 y4)
  thus ?case using y8  waypoints_wf_def[of win] by auto
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

lemma waypoint_window_all_but_last_found_aux:"waypoints_window ws i len = Some win \<Longrightarrow> \<forall> j. j < len - 1 \<longrightarrow> Some (win ! j) = find_waypoint ws (get_number (win ! j))"
proof(induct len arbitrary: i win)
  case 0
  then show ?case by auto
next
  case (Suc len)
  then have "len = 0 \<or> 0 < len" by auto
  thus ?case 
  proof 
    assume "len = 0"
    thus ?case by auto
  next
    assume a:"len > 0"
    then obtain win' w where y1:"Some w = find_waypoint ws i" and y2:"waypoints_window ws (get_nextwp w) len = Some win'" and y3:"w # win' = win" using Suc
      by (metis Suc_pred WaypointManager.waypoints_window_elim9 WaypointManager_axioms waypoints_window_elim8)
    then have y4:"\<forall>j<len - 1. Some (win' ! j) = find_waypoint ws (get_number (win' ! j))" using Suc by auto
    thus ?case using a y1 y2 y3 
      by (metis Suc_less_eq Suc_pred' find_waypoint_correct neq0_conv nth_Cons_0 nth_Cons_Suc)
  qed
qed    

lemma waypoint_window_all_but_last_found:"waypoints_window ws i len = Some win \<Longrightarrow> j < len - 1 \<Longrightarrow> Some (win ! j) = find_waypoint ws (get_number (win ! j))"
  using waypoint_window_all_but_last_found_aux by blast
    
lemma waypoints_window_success_all_nextwp_in_source:"waypoints_window ws i len = Some win \<Longrightarrow> a < len \<Longrightarrow> \<exists> w. Some w = find_waypoint ws (get_nextwp (win ! a))"
proof (induct win arbitrary: i len a)
  case Nil
  then show ?case by (meson WaypointManager.waypoints_window_not_empty WaypointManager_axioms)
next
  case (Cons w win)
  then have "1 = len \<or> 1 < len" using waypoints_window_elim12 by auto
  thus ?case
  proof
    assume "1 = len"
    thus ?case using waypoints_window_elim11
      by (metis (no_types, lifting) Cons.prems(1) Cons.prems(2) One_nat_def correct_update1 less_numeral_extra(4) less_trans_Suc linorder_neqE_nat not_less_zero nth_Cons_0)
  next
    assume "1 < len"
    then obtain n where y1:"len = Suc (Suc n)" by (metis One_nat_def lessE)
    then have y2:"waypoints_window ws i (Suc (Suc n)) = Some (w # win)" using Cons by auto
    then have y3:"Some w = find_waypoint ws i" and y4:"waypoints_window ws (get_nextwp w) (Suc n) = Some win" using Cons waypoints_window_elim12[OF y2] by auto
    then have y5:"(a - 1) < Suc n"  using Cons.prems(2) y1 by linarith
    thus ?case using Cons(1)[OF y4 y5] y3 Cons(2) by (metis not_None_eq nth_Cons' waypoints_window_intro3 y4)
  qed
qed  

end
  
end