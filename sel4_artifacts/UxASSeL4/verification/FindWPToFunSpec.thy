theory FindWPToFunSpec imports 
"LoadCode"
"WaypointManagerFunSpec"
begin

interpretation FindWaypoint get_waypoint_number done

(* Lift waypoints from a mission command into a list with the same order. *)
fun lift_waypoints  where
  "lift_waypoints s mcp 0 = []"
| "lift_waypoints s mcp (Suc n) = lift_waypoints s mcp n @ [get_waypoint s mcp n]" 

(* lift_waypoints maintains the size waypoints lifted. *)
lemma lift_waypoints_length: "ws = lift_waypoints s mcp n \<Longrightarrow> length ws = n"
  apply(induct n arbitrary: ws) by auto  

(* One can use nth to get waypoint i indirectly through lift_waypoints. *)
lemma lift_waypoints_to_get_waypoint: 
  "ws = lift_waypoints s mcp n \<Longrightarrow> \<forall> k< n.  get_waypoint s mcp k = nth ws k"
apply(induct n arbitrary: ws) by (auto simp add: less_Suc_eq lift_waypoints_length nth_append)

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

(* lift_waypoint will create prefixes when s and mcp are fixed and the sizes differ. *)  
lemma lifted_waypoint_prefixes:" i \<le> j \<Longrightarrow> prefix (lift_waypoints s mcp i) (lift_waypoints s mcp j)"
apply(induct i) by (metis lift_waypoints.simps(2) prefix_def prefix_order.lift_Suc_mono_le)+    
    
lemma find_waypoint_next_is_match:
assumes a1:"Some w = find_waypoint (lift_waypoints s mcp (unat i)) (get_waypoint_number(get_waypoint s mcp (uint j)))"
and  a2:"None = find_waypoint (lift_waypoints s mcp (unat j)) (get_waypoint_number (get_waypoint s mcp (uint j)))"
and a3:"j < i"
shows "get_waypoint s mcp (uint j) = w"
proof -  
  have y1:"prefix (lift_waypoints s mcp (unat j) @ [get_waypoint s mcp (uint j)]) (lift_waypoints s mcp (unat i))" 
    by (metis lifted_waypoint_prefixes  lift_waypoints.simps(2) a3 le_less less_antisym not_less uint_nat word_less_nat_alt )
  then have y2:"Some (get_waypoint s mcp (uint j)) = find_waypoint (lift_waypoints s mcp (unat j) @ [get_waypoint s mcp (uint j)]) (get_waypoint_number (get_waypoint s mcp (uint j)))"
    using a2 find_waypoint_none_extend_some by auto
  show ?thesis using find_waypoint_ignores_dup_matches y1 y2 a1 by (metis option.inject)
qed 

lemma [simp]: "j < i \<Longrightarrow> int (unat j) = uint j" by (simp add: uint_nat)
  
lemma find_waypoint_extend_failure:
  assumes a1:"None = find_waypoint (lift_waypoints s mcp (unat (j::32 word))) i"
and a2:"number_C (get_waypoint s mcp (uint j)) \<noteq> i"
and a3:"j < k"
shows "None = find_waypoint (lift_waypoints s mcp (unat (j + 1))) i"
proof -
  have y1:"None = find_waypoint ( lift_waypoints s mcp (unat j) @ [get_waypoint s mcp (uint j)]) i" 
    by (metis get_waypoint_number_def a1 a2 find_waypoint_none_extend)
  then have y2:"None = find_waypoint (lift_waypoints s mcp (Suc (unat j))) i" by (simp add: uint_nat)
  then have y3:"(unat j) + 1 = unat (j + 1)" using a3 
    by (metis Suc_eq_plus1 add.commute less_is_non_zero_p1 unatSuc)
  thus ?thesis using Suc_eq_plus1 y2 by presburger
qed
  
lemma findwp_success:
"\<lbrace> \<lambda> (s::lifted_globals).
  is_valid_MissionCommand s mcp
  \<and> Some w = find_waypoint (lift_waypoints s mcp (unat (get_waypoints_length s mcp))) i
  \<and> P s\<rbrace>
   LoadCode.MissionCommandUtils.FindWP' mcp i
\<lbrace> \<lambda> r s. heap_Waypoint_struct_C s r = w \<and> P s\<rbrace>!"
  apply (unfold LoadCode.MissionCommandUtils.FindWP'_def)
  apply (simp add: skipE_def)
  apply(subst whileLoopE_add_inv[where M = "\<lambda> (j,s). unat (get_waypoints_length s mcp - j)"
                                 and I = "\<lambda> j s. P s 
\<and> is_valid_MissionCommand s mcp
\<and> Some w = find_waypoint (lift_waypoints s mcp (unat (get_waypoints_length s mcp))) i
\<and> None = find_waypoint (lift_waypoints s mcp (unat j)) i
\<and> j \<le> get_waypoints_length s mcp
"])
   apply wp
   apply (simp add: is_valid_MissionCommand_def word_less_nat_alt)+
     apply rule+
     apply (intro find_waypoint_next_is_match)
       using inc_le apply blast+
     using find_waypoint_extend_failure word_less_nat_alt apply blast
    apply (metis uint_nat)
   apply clarsimp
   apply rule
    apply (metis find_waypoint_extend_failure get_waypoint_number_def word_less_nat_alt)
   apply rule
    using inc_le word_less_nat_alt apply blast
   apply (metis (no_types, hide_lams) diff_diff_add linorder_not_less measure_unat order_le_less right_minus_eq uint_nat)
  apply fastforce
 apply wp
 by (simp add: find_waypoint_def is_valid_MissionCommand_def)

lemma find_waypoint_failure_not_equal_all_elems_aux:"None = find_waypoint (lift_waypoints s mcp (unat (get_waypoints_length s mcp))) n 
\<Longrightarrow> \<forall> i < get_waypoints_length s mcp. number_C (get_waypoint s mcp (int (unat i))) \<noteq> n"
proof -
  assume a:"None = find_waypoint (lift_waypoints s mcp (unat (get_waypoints_length s mcp))) n"
  then obtain ws where y1:"ws = lift_waypoints s mcp (unat (get_waypoints_length s mcp))" and y2:"None = find_waypoint ws n" by auto
  then have "\<forall>i<length ws. number_C (ws ! i) \<noteq> n" using find_waypoint_failure_not_equal_all_elems y2 by auto
  then have "\<forall>i<unat (get_waypoints_length s mcp). number_C (ws ! i) \<noteq> n" using lift_waypoints_length[OF y1] by auto
  then have "\<forall>i<unat (get_waypoints_length s mcp). number_C (get_waypoint s mcp (int i)) \<noteq> n" using lift_waypoints_to_get_waypoint[OF y1] by auto
  thus ?thesis by (metis of_nat_less_iff uint_nat word_less_def)
qed
  
lemma findwp_failure:
"\<lbrace> \<lambda> (s::lifted_globals).
  is_valid_MissionCommand s mcp
  \<and> None = find_waypoint (lift_waypoints s mcp (unat (get_waypoints_length s mcp))) i
  \<and> P s\<rbrace>
  LoadCode.MissionCommandUtils.FindWP' mcp i
\<lbrace> \<lambda> r s. r = NULL \<and> P s\<rbrace>!"
 apply (unfold LoadCode.MissionCommandUtils.FindWP'_def)
 apply (simp add: skipE_def)
 apply(subst whileLoopE_add_inv[where M = "\<lambda> (j,s). unat (get_waypoints_length s mcp - j)"
                                 and I = "\<lambda> j s. P s 
\<and> is_valid_MissionCommand s mcp
\<and> None = find_waypoint (lift_waypoints s mcp (unat (get_waypoints_length s mcp))) i
"])
 apply wp
   apply clarsimp
   apply (metis find_waypoint_failure_not_equal_all_elems_aux get_waypoint_number_def is_valid_MissionCommand_def uint_nat word_less_nat_alt)
  apply simp
  apply wp 
  using is_valid_MissionCommand_def by blast

lemma aux1:"None = find_waypoint (lift_waypoints s mcp (unat j)) i \<Longrightarrow>
           j < get_waypoints_length s mcp \<Longrightarrow>
           get_waypoint_number (get_waypoint s mcp (uint j)) = i \<Longrightarrow>
           Some (get_waypoint s mcp (uint j)) = find_waypoint (lift_waypoints s mcp (unat (get_waypoints_length s mcp))) i"
  by (metis find_waypoint_failure_not_equal_all_elems_aux find_waypoint_next_is_match get_waypoint_number_def not_None_eq uint_nat)
    
lemma findwp_to_funspec:
"\<lbrace> \<lambda> (s::lifted_globals).
  is_valid_MissionCommand s mcp \<and> P s\<rbrace>
  LoadCode.MissionCommandUtils.FindWP' mcp i
\<lbrace> \<lambda> r s. P s \<and> (r = NULL \<and> None = find_waypoint (lift_waypoints s mcp (unat (get_waypoints_length s mcp))) i) 
          \<or> ( r \<noteq> NULL \<and> is_valid_Waypoint_struct_C s r 
              \<and> Some (heap_Waypoint_struct_C s r) = find_waypoint (lift_waypoints s mcp (unat (get_waypoints_length s mcp))) i) \<rbrace>!"
 apply (unfold LoadCode.MissionCommandUtils.FindWP'_def)
 apply (simp add: skipE_def)
 apply(subst whileLoopE_add_inv[where M = "\<lambda> (j,s). unat (get_waypoints_length s mcp - j)"
                                 and I = 
"\<lambda> j s. P s 
\<and> is_valid_MissionCommand s mcp
\<and> None = find_waypoint (lift_waypoints s mcp (unat j)) i
\<and> (get_waypoint_number (get_waypoint s mcp (uint j)) = i \<or> get_waypoint_number (get_waypoint s mcp (uint j)) \<noteq> i)
\<and> j \<le> get_waypoints_length s mcp
\<and> 0 \<le> unat j
"])
   apply wp+
    apply (clarsimp)
    apply (rule+,metis is_valid_MissionCommand_def uint_nat word_less_nat_alt)
    apply rule
       apply (metis is_valid_MissionCommand_def uint_nat word_less_nat_alt)
         apply (intro aux1,simp+)
     apply (metis is_valid_MissionCommand_def uint_nat word_less_nat_alt)
    apply rule+
    apply (metis find_waypoint_extend_failure get_waypoint_number_def)
  using inc_le apply (rule,blast)
    apply (metis is_valid_MissionCommand_def uint_nat word_less_nat_alt)
   apply clarsimp
  apply wp
  apply clarsimp
    by (simp add: find_waypoint_def is_valid_MissionCommand_def)
end