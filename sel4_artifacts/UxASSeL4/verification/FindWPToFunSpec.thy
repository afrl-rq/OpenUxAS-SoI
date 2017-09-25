theory FindWPToFunSpec imports 
"LoadCode"
"WaypointManagerFunSpec"
begin

interpretation WaypointManager get_waypoint_number nextwaypoint_C done

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
    
lemma lift_waypoint_to_take:
  "ws = lift_waypoints s mcp i \<Longrightarrow> j < i \<Longrightarrow> take j ws = lift_waypoints s mcp j"
proof(induct j arbitrary: ws)
  case 0
  then show ?case by auto
next
  case (Suc j)
  then have "take j ws = lift_waypoints s mcp j" by auto
  thus ?case using Suc
    by (metis Suc_lessD lift_waypoints.simps(2) lift_waypoints_length lift_waypoints_to_get_waypoint 
        take_Suc_conv_app_nth)
qed
  
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

lemma find_waypoint_failure_all_neq_number:"ws = lift_waypoints s mcp (unat (get_waypoints_length s mcp)) 
\<Longrightarrow> None = find_waypoint ws n
\<Longrightarrow> \<forall>i<unat (get_waypoints_length s mcp). number_C (get_waypoint s mcp (int i)) \<noteq> n"
  by (metis find_waypoint_failure_not_equal_all_elems 
      get_waypoint_number_def lift_waypoints_length lift_waypoints_to_get_waypoint)

lemma valid_mission_command[simp]:
"is_valid_MissionCommand s mcp 
\<Longrightarrow> j < get_waypoints_length s mcp
\<Longrightarrow> is_valid_MissionCommand_struct_C s mcp 
  \<and> is_valid_Waypoint_struct_C s (get_waypoint_ptr s mcp (uint j)) 
  \<and> is_valid_Waypoint_struct_C'ptr s (get_waypoint_ptr_ptr s mcp (uint j)) 
  \<and> is_valid_MissionCommand_struct_C s mcp"
  apply(unfold is_valid_MissionCommand_def) by (metis uint_nat word_less_nat_alt)  
  
lemma findwp_success:
"\<lbrace> \<lambda> (s::lifted_globals).
  is_valid_MissionCommand s mcp
  \<and> Some w = find_waypoint (lift_waypoints s mcp (unat (get_waypoints_length s mcp))) i
  \<and> P s\<rbrace>
   LoadCode.MissionCommandUtils.FindWP' mcp i
\<lbrace> \<lambda> r s. heap_Waypoint_struct_C s r = w \<and> P s\<rbrace>!"
  apply (unfold LoadCode.MissionCommandUtils.FindWP'_def)
  apply (simp add: skipE_def)
  apply(subst whileLoopE_add_inv
        [where 
          M = "\<lambda> (j,s). unat (get_waypoints_length s mcp - j)"
          and I = 
            "\<lambda> j s. P s 
            \<and> is_valid_MissionCommand s mcp
            \<and> Some w = find_waypoint (lift_waypoints s mcp (unat (get_waypoints_length s mcp))) i
            \<and> None = find_waypoint (lift_waypoints s mcp (unat j)) i
            \<and> j \<le> get_waypoints_length s mcp"
        ])
  apply wp
    apply clarsimp
    apply rule+
     apply (metis find_waypoint_next_is_match lift_waypoints_length 
      lift_waypoints_to_get_waypoint lift_waypoint_to_take uint_nat unat_mono)
    apply (metis find_waypoint_extend_failure get_waypoint_number_def inc_le) 
   apply force
  apply wp
  using find_waypoint_def is_valid_MissionCommand_def by auto
  
lemma findwp_failure:
"\<lbrace> \<lambda> (s::lifted_globals).
  P s
  \<and> is_valid_MissionCommand s mcp
  \<and> None = find_waypoint (lift_waypoints s mcp (unat (get_waypoints_length s mcp))) i \<rbrace>
  LoadCode.MissionCommandUtils.FindWP' mcp i
\<lbrace> \<lambda> r s. P s \<and> r = NULL \<rbrace>!"
  apply (unfold LoadCode.MissionCommandUtils.FindWP'_def)
  apply (simp add: skipE_def)
  apply(subst whileLoopE_add_inv
        [where 
          M = "\<lambda> (j,s). unat (get_waypoints_length s mcp - j)"
          and I = "\<lambda> j s. P s 
                          \<and> is_valid_MissionCommand s mcp
                          \<and> None 
                            = find_waypoint 
                                (lift_waypoints s mcp (unat (get_waypoints_length s mcp))) 
                                i"
        ])
 apply wp
    apply clarsimp
    apply (metis find_waypoint_failure_all_neq_number get_waypoint_number_def 
                 uint_nat word_less_nat_alt)
  apply simp
  apply wp
  using is_valid_MissionCommand_def by auto
    
lemma findwp_to_funspec:
"\<lbrace> \<lambda> (s::lifted_globals).
  P s
  \<and> is_valid_MissionCommand s mcp\<rbrace>
  LoadCode.MissionCommandUtils.FindWP' mcp i
\<lbrace> \<lambda> r s. 
  P s 
  \<and> r = NULL \<longrightarrow> None = find_waypoint (lift_waypoints s mcp (unat (get_waypoints_length s mcp))) i
  \<and> r \<noteq> NULL 
    \<longrightarrow> is_valid_Waypoint_struct_C s r 
        \<and> Some (heap_Waypoint_struct_C s r) 
          = find_waypoint (lift_waypoints s mcp (unat (get_waypoints_length s mcp))) i \<rbrace>!"
 apply (unfold LoadCode.MissionCommandUtils.FindWP'_def)
 apply (simp add: skipE_def)
 apply(subst whileLoopE_add_inv
      [where 
          M = "\<lambda> (j,s). unat (get_waypoints_length s mcp - j)"
          and I = 
            "\<lambda> j s. P s 
             \<and> is_valid_MissionCommand s mcp
             \<and> None = find_waypoint (lift_waypoints s mcp (unat j)) i
             \<and> (get_waypoint_number (get_waypoint s mcp (uint j)) = i 
                \<or> get_waypoint_number (get_waypoint s mcp (uint j)) \<noteq> i)
             \<and> j \<le> get_waypoints_length s mcp"
      ])
  apply wp
    apply clarsimp
    apply (metis find_waypoint_extend_failure get_waypoint_number_def inc_le)
    apply blast
  apply wp
  using find_waypoint_def is_valid_MissionCommand_def by auto

lemma MCWaypointSubSequence_to_funspec:
"\<lbrace> \<lambda> (s::lifted_globals).
  P s
  \<and> is_valid_MissionCommand s mcp
  \<and> ws = lift_waypoints s mcp (unat (get_waypoints_length s mcp))
  \<and> waypoints_wf ws
\<rbrace>
  LoadCode.MissionCommandUtils.MCWaypointSubSequence' mcp i n mcpe 
\<lbrace> \<lambda> r s. 
  P s 
  \<and> r = 1 \<longrightarrow> (\<exists> rmcp. rmcp = (ptr_coerce mcpe) \<and> Some (lift_waypoints s rmcp (unat (get_waypoints_length s rmcp))) = waypoints_window ws i (unat n)) \<rbrace>!"    
 apply (unfold LoadCode.MissionCommandUtils.MCWaypointSubSequence'_def)
  apply (simp add: skipE_def)
              apply(simp add: unlessE_def)
  apply wp 

          apply clarsimp

end