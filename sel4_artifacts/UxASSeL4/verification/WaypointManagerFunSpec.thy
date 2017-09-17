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

lemma find_waypoint_none_extend: 
"None = find_waypoint ws i \<Longrightarrow> get_number w \<noteq> i  \<Longrightarrow> None = find_waypoint (ws @[w]) i"
apply(induct ws) using find_waypoint_def by auto
  
lemma find_waypoint_none_extend_some: 
"None = find_waypoint ws i \<Longrightarrow> get_number w = i \<Longrightarrow> Some w = find_waypoint (ws @[w]) i"
  apply(induct ws) using find_waypoint_def by auto     
    
lemma find_waypoint_succuss:"Some w = find_waypoint ws i \<Longrightarrow> \<exists> j. j < length ws \<and> w = ws ! j \<and> i = get_number w"
  apply(induct ws)
   apply (simp add: find_waypoint_def)
    by (metis (mono_tags, lifting) find_Some_iff find_waypoint_def)    

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

definition waypoints_wf where
  "waypoints_wf ws \<equiv> (\<forall> w'. List.member ws w' \<longrightarrow> (\<exists> w. Some w = find_waypoint ws (get_nextwp w')))"

  
fun waypoints_window :: "'w list \<Rightarrow> 'id \<Rightarrow> nat \<Rightarrow> ('w list) option" where
  "waypoints_window ws i 0 = Some []"
| "waypoints_window ws i (Suc n) = 
    (case find_waypoint ws i of
     Some w \<Rightarrow> 
       if get_nextwp w = i then Some [w]
       else 
        (case waypoints_window ws (get_nextwp w) n of 
         Some ws \<Rightarrow> Some (w # ws) 
         | None \<Rightarrow> None)
    | None \<Rightarrow> None)"

  
(*
lemma  "waypoints_wf ws \<Longrightarrow> Some w = find_waypoint ws i \<Longrightarrow> \<exists> win. Some win = waypoints_window ws i len"
  apply(unfold find_waypoint_def)
    apply(induct rule:find.induct)
    
lemma waypoints_window_lteq_len:"waypoints_wf ws \<Longrightarrow> Some w = find_waypoint ws i \<Longrightarrow> win = waypoints_window ws i len \<Longrightarrow> length win \<le> len"
  proof(induct len)
    case 0
    then show ?case by auto
  next
    case (Suc len)
    then have "length win \<le> len" sledgehammer[z3 e spass]
    then show ?case
  qed 
   apply clarsimp
*)
    
end
  

  
end