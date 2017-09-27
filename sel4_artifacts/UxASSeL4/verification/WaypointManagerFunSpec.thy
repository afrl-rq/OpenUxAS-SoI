theory WaypointManagerFunSpec imports 
Main
Sublist
begin
  
locale WaypointManager =
  fixes get_number :: "'w \<Rightarrow> 'id"
   fixes get_nextwp :: "'w \<Rightarrow> 'id"
context WaypointManager begin

(* FUNSPEC(find_wp): Find a waypoint in a list of waypoints by its number. This is how we 
   notionally expect the find_wp function to work. *)
definition find_waypoint :: "'w list \<Rightarrow> 'id \<Rightarrow> 'w option" where
"find_waypoint ws i \<equiv> List.find (\<lambda> w. get_number w = i) ws" 

fun find_waypoint_aux where
  "find_waypoint_aux [] _ = None"
| "find_waypoint_aux (x#xs) i = (if get_number x = i then Some x else find_waypoint_aux xs i)"

lemma stuff:"find_waypoint_aux xs i = Some x \<Longrightarrow> get_number x = i"
  apply(induct xs arbitrary:i)
   apply auto
    by (metis option.inject)
      
lemma "x = find_waypoint_aux ws i \<Longrightarrow> x = find_waypoint ws i"
  proof(induct ws arbitrary: i)
    case Nil
    then show ?case using find_waypoint_def by auto
  next
    case (Cons a ws)
    then have "x = Some a \<or> x \<noteq> Some a" by auto
    thus ?case
    proof 
      assume a:"x = Some a"
      then have "get_number a = i" using Cons stuff by presburger 
      thus ?case using Cons a by (simp add: find_waypoint_def)
    next 
      assume a:"x \<noteq> Some a"
      then have "get_number a \<noteq> i" using Cons by auto
      thus ?case using a Cons find_waypoint_def by auto
    qed
qed

lemma "x = find_waypoint ws i \<Longrightarrow> x = find_waypoint_aux ws i"
  apply(induct ws arbitrary: i)
  by (simp add: find_waypoint_def)+

lemma "x = find_waypoint_aux ws i \<Longrightarrow> x = find_waypoint ws i"
  apply(induct ws arbitrary: i)
  by (simp add: find_waypoint_def)+
      
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
  using WaypointManager.find_waypoint_success_construction in_set_member by fastforce

definition waypoints_wf where
  "waypoints_wf ws \<equiv> (\<forall> w'. List.member ws w' \<longrightarrow> (\<exists> w. Some w = find_waypoint ws (get_nextwp w')))"
  
inductive waypoints_window_ind :: "'w list \<Rightarrow> 'id \<Rightarrow> nat \<Rightarrow> ('w list) option \<Rightarrow> bool" where
 "find_waypoint ws i = None \<Longrightarrow> waypoints_window_ind ws i n None"
| "find_waypoint ws i = Some w 
  \<Longrightarrow> get_nextwp w \<noteq> i
  \<Longrightarrow> waypoints_window_ind ws (get_nextwp w) n None 
  \<Longrightarrow> waypoints_window_ind ws i (Suc n) None"
| "find_waypoint ws i = Some w \<Longrightarrow> waypoints_window_ind ws i 0 (Some [])"
| "find_waypoint ws i = Some w \<Longrightarrow> get_nextwp w = i \<Longrightarrow> waypoints_window_ind ws i (Suc n) (Some [w])"
| "find_waypoint ws i = Some w 
  \<Longrightarrow> get_nextwp w \<noteq> i 
  \<Longrightarrow> waypoints_window_ind ws (get_nextwp w) n (Some ws') 
  \<Longrightarrow> waypoints_window_ind ws i (Suc n) (Some (w # ws'))"

(* If a zero sized window cant be found then the waypoint corresponding to i cannot be found. *)
lemma waypoints_window_ind_zero_none_find_waypoint_none:"waypoints_window_ind ws i 0 None \<Longrightarrow> None = find_waypoint ws i"
  apply(cases rule:waypoints_window_ind.cases) by auto

(* If a zero sized window can be found then the waypoint corresponding to i can be found. *)    
lemma waypoints_window_ind_zero_some_find_waypoint_some:"waypoints_window_ind ws i 0 (Some ws') \<Longrightarrow> \<exists> w. Some w = find_waypoint ws i"
  apply(cases rule:waypoints_window_ind.cases) by auto

(* If you couldnt get a window for some size you cant get a larger window. *)    
lemma waypoints_window_ind_none_extend:"waypoints_window_ind ws i n' None \<Longrightarrow> \<forall> n>n'. waypoints_window_ind ws i n' None"
  apply(induct "n'" arbitrary: i) by auto

(* If you cant get the first waypoint you cant get a window for any size. *)
lemma find_waypoint_none_waypoints_window_ind_none:"find_waypoint ws i = None \<Longrightarrow> waypoints_window_ind ws i n win \<Longrightarrow> win = None"    
  apply(cases rule:waypoints_window_ind.cases) by auto

(* If you get a zero sized window it is empty. *)    
lemma waypoints_window_ind_zero_some:"waypoints_window_ind ws i 0 (Some ws') \<Longrightarrow> ws' = []"
  apply(cases rule:waypoints_window_ind.cases) by auto

(* If you have a zero sized window you have a window size of 1. *)
lemma waypoints_window_ind_zero_some_extend:
  assumes a1:"waypoints_window_ind ws i 0 (Some [])"
  and a2:"find_waypoint ws i = Some w"
shows "Ex (waypoints_window_ind ws i (Suc 0))"
  by (metis (full_types) not_Some_eq waypoints_window_ind.intros)  

(* TODO: Not sure what to say about this. *)
lemma waypoints_window_ind_extend:"waypoints_window_ind ws i n winopt \<Longrightarrow> \<exists>winopt. waypoints_window_ind ws i (Suc n) winopt"
  apply(induct rule:waypoints_window_ind.induct)
   by (metis split_option_ex waypoints_window_ind.intros waypoints_window_ind_zero_some_extend)+

(* Self-explanatory. *)
lemma waypoints_window_ind_is_injective:"\<exists> winopt. waypoints_window_ind ws i n winopt"
  apply(induct n)
   apply(cases "find_waypoint ws i")
   by (meson WaypointManager.waypoints_window_ind.intros waypoints_window_ind_extend)+

(* Cases that cause a window failure. *)
lemma waypoints_window_ind_none_cases:"waypoints_window_ind ws i n None 
\<Longrightarrow> None = find_waypoint ws i \<or> (\<exists> w. Some w = find_waypoint ws i \<and> get_nextwp w \<noteq> i \<and> waypoints_window_ind ws (get_nextwp w) (n - 1) None)"
  apply(cases rule:waypoints_window_ind.cases) by auto

(* self-explanatory. *)
lemma waypoints_window_ind_is_deterministic:"waypoints_window_ind ws i n winopt' \<Longrightarrow> waypoints_window_ind ws i n winopt \<Longrightarrow> winopt' = winopt"
proof(induct n arbitrary: i winopt winopt')
  case 0
  then show ?case by (metis (full_types) WaypointManager.waypoints_window_ind_zero_none_find_waypoint_none WaypointManager.waypoints_window_ind_zero_some not_None_eq waypoints_window_ind_zero_some_find_waypoint_some)
next
  case (Suc n)
  thus ?case
  proof(cases rule:waypoints_window_ind.cases[OF Suc(2)])
    case (1 ws i n)
    then show ?thesis  by (cases rule:waypoints_window_ind.cases[OF Suc(3)],auto)
  next
    case (2 ws i w n)
    then show ?thesis using Suc  by (cases rule:waypoints_window_ind.cases[OF Suc(3)],auto)
  next
    case (3 ws i w)
    then show ?thesis  by (cases rule:waypoints_window_ind.cases[OF Suc(3)],auto)
  next
    case (4 ws i w n)
    then show ?thesis  by (cases rule:waypoints_window_ind.cases[OF Suc(3)],auto)
  next
    case (5 ws i w n ws')
    then show ?thesis  using Suc by (cases rule:waypoints_window_ind.cases[OF Suc(3)],auto)
  qed 
qed    

fun "waypoints_window" where
"waypoints_window ws i n = (SOME p. waypoints_window_ind ws i n p)"

(* If the waypoint list is well-formed and you can find a waypoint in the list then you can find the next waypoint in the list. *)
lemma waypoints_wf_membership:"waypoints_wf ws \<Longrightarrow> Some w' = find_waypoint ws i \<Longrightarrow> \<exists> w. Some w = find_waypoint ws (get_nextwp w')"
  apply(unfold waypoints_wf_def) by (simp add: WaypointManager.find_waypoint_success_membership)

(* The only way an empty window is found is if the window size is 0. *)
lemma waypoints_window_ind_success_empty_zero_length:"waypoints_window_ind ws i n (Some []) \<Longrightarrow> n = 0"
  apply(cases rule:waypoints_window_ind.cases) by auto

(* If you find window with a size greater than one than you can get a smaller window or you are at the last waypoint. *)    
lemma waypoints_window_ind_success_length_gt_one:"waypoints_window_ind ws i n (Some win) \<Longrightarrow> length win > 0 \<Longrightarrow> \<exists> w. waypoints_window_ind ws (get_nextwp w) (n - 1) (Some (tl win)) \<or> get_nextwp w = i"
  apply(induct win)
    apply (cases rule:waypoints_window_ind.cases)
        apply auto
        apply (cases rule:waypoints_window_ind.cases)
    by auto

lemma waypoints_window_lteq_len_aux:"waypoints_window_ind ws i len out \<Longrightarrow> out = Some win \<Longrightarrow> waypoints_wf ws \<Longrightarrow> Some w = find_waypoint ws i \<Longrightarrow> length win \<le> len"
  proof(induct arbitrary: win w rule:waypoints_window_ind.induct)
    case (1 ws i n)
    then show ?case by auto
  next
    case (2 ws i w n)
    then show ?case by auto
  next
    case (3 ws i w)
    then show ?case by auto
  next
    case (4 ws i w n)
    then show ?case by auto
  next
    case (5 ws i w' n ws')
    then obtain x where "Some x = find_waypoint ws (get_nextwp w')" by (metis WaypointManager.waypoints_wf_membership)
    then have "length ws' \<le> n" using 5 by auto
    thus ?case using 5 by auto
  qed

lemma waypoints_window_lteq_len:"waypoints_wf ws \<Longrightarrow> Some w = find_waypoint ws i \<Longrightarrow> Some win = waypoints_window ws i len \<Longrightarrow> length win \<le> len"
  using   waypoints_window_lteq_len_aux 
  by (metis tfl_some waypoints_window.simps waypoints_window_ind_is_injective)

end
  
end