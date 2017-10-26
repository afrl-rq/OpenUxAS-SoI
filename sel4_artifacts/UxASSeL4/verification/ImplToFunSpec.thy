theory ImplToFunSpec imports 
"LoadCode"
"WaypointManagerFunSpec"
begin

definition nextwp_update where
"nextwp_update w i \<equiv>   nextwaypoint_C_update (\<lambda> _. i) w"

interpretation WaypointManager get_waypoint_number nextwaypoint_C nextwp_update
  apply unfold_locales
    apply (auto simp add: nextwp_update_def)
  using Waypoint_struct_C_accupd_diff(131) get_waypoint_number_def nextwp_update_def apply presburger  
  done
    
    
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
\<lbrace> \<lambda> r s.   is_valid_MissionCommand s mcp
  \<and> Some w = find_waypoint (lift_waypoints s mcp (unat (get_waypoints_length s mcp))) i \<and> P s \<and> heap_Waypoint_struct_C s r = w\<rbrace>!"
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
  is_valid_MissionCommand s mcp
  \<and> P s \<rbrace>
  LoadCode.MissionCommandUtils.FindWP' mcp i
\<lbrace> \<lambda> r s. 
  
  r = NULL \<longrightarrow> None = find_waypoint (lift_waypoints s mcp (unat (get_waypoints_length s mcp))) i
  \<and> r \<noteq> NULL 
    \<longrightarrow> is_valid_Waypoint_struct_C s r 
        \<and> Some (heap_Waypoint_struct_C s r) 
          = find_waypoint (lift_waypoints s mcp (unat (get_waypoints_length s mcp))) i 
  \<and> P s\<rbrace>!"
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

lemma max_word16[simp]:"(max_word::16 word) = 65535"    
  apply(unfold max_word_def) by auto

lemma word16_leq_max_word16:"uint (a::16 word) \<le> 65535"
  using word.uint[of a] by auto
    
lemma word16_leq_max_word32:"uint (a::16 word) \<le> 2147483648"
  using word.uint[of a] by auto
    
theorem validNF_bind_return:"\<lbrace> A \<rbrace> g f \<lbrace>B\<rbrace>! \<Longrightarrow> \<lbrace>A\<rbrace> (return f) >>= g \<lbrace>B\<rbrace>!"   
  apply (rule validNF_bind[ where B="\<lambda> r s. A s \<and> r = f"])
   apply (simp add: triple_judgement_def validNF_is_triple)
    by (smt hoare_return_simp no_fail_pre no_fail_return validNF)

theorem validNF_bind_gets:"\<forall> r. \<lbrace> \<lambda> s. A s \<and> r = f s \<rbrace> g r \<lbrace>B\<rbrace>! \<Longrightarrow> \<lbrace>A\<rbrace> do x \<leftarrow> gets f; g x od\<lbrace>B\<rbrace>!"   
  apply (rule validNF_bind[ where B="\<lambda> r s. A s \<and> r = f s"])
   apply simp
  by (simp add: hoare_gets validNF)

theorem validNF_ignbind_modify:"\<forall> s. A (f s) = A s \<Longrightarrow> \<forall> r. \<lbrace> \<lambda> s. A (f s) \<rbrace> g \<lbrace>B\<rbrace>! \<Longrightarrow> \<lbrace>A\<rbrace> do x \<leftarrow> modify f; g od\<lbrace>B\<rbrace>!"   
  apply (rule validNF_bind[ where B="\<lambda> r s. A (f s)"])
   apply simp
    by (metis hoare_modifyE_var no_fail_def no_fail_modify validNF)
      
      
lemma validNF_nobind_guard:" \<forall> s. P s \<longrightarrow> Q s \<Longrightarrow> \<lbrace> P \<rbrace> S \<lbrace> R \<rbrace>! \<Longrightarrow> \<lbrace> P \<rbrace> do guard Q; S od \<lbrace> R \<rbrace>!"
  apply wp by (simp add: guard_def validNF_alt_def)
    
lemma validNF_bind_guard:" \<forall> s. P s \<longrightarrow> Q s \<Longrightarrow> \<lbrace> P \<rbrace> S  \<lbrace> R \<rbrace>! \<Longrightarrow> \<lbrace> P \<rbrace> do x \<leftarrow> guard Q; S od \<lbrace> R \<rbrace>!"
  apply wp by (simp add: guard_def validNF_alt_def)
    
lemma validNF_bind_FindWP:
"\<forall> r. \<lbrace>\<lambda> s. is_valid_MissionCommand s mcp \<and> Some w = find_waypoint (lift_waypoints s mcp (unat (get_waypoints_length s mcp))) i \<and> P s \<and> heap_Waypoint_struct_C s r = w\<rbrace> S r \<lbrace> R \<rbrace>! 
\<Longrightarrow> \<lbrace> \<lambda> s. is_valid_MissionCommand s mcp \<and> Some w = find_waypoint (lift_waypoints s mcp (unat (get_waypoints_length s mcp))) i \<and> P s\<rbrace> do x  \<leftarrow> LoadCode.MissionCommandUtils.FindWP' mcp i; S x od \<lbrace> R \<rbrace>!"
  apply (rule validNF_bind[where B="\<lambda> r s. is_valid_MissionCommand s mcp \<and> Some w = find_waypoint (lift_waypoints s mcp (unat (get_waypoints_length s mcp))) i \<and> P s \<and> heap_Waypoint_struct_C s r = w"])
   apply auto
  by (rule findwp_success)
  
lemma test:"(\<forall> s. P s \<longrightarrow> (\<exists> w. find_waypoint (lift_waypoints s mcp (unat (get_waypoints_length s mcp))) i = Some w))
\<Longrightarrow> (\<forall> s. P s \<longrightarrow> (\<forall> r. (heap_Waypoint_struct_C s r) = w \<and> Q r s)) \<Longrightarrow>
\<lbrace>  P \<rbrace> MissionCommandUtils.FindWP' mcp i \<lbrace> Q \<rbrace>!"
  sorry
        
lemma validNF_bind_rev: "\<lbrace>A\<rbrace> f \<lbrace>B\<rbrace>! \<Longrightarrow> (\<And>x. \<lbrace>B x\<rbrace> g x \<lbrace>C\<rbrace>!) \<Longrightarrow> \<lbrace>A\<rbrace> f >>= g \<lbrace>C\<rbrace>!"
  by (rule validNF_bind)

(* Structures must be packed! *)
lemma ac_bug_nextwaypoint_update[simp]:"P s[wsp +\<^sub>p j \<rightarrow>nextwaypoint :=  w] = P s[wsp +\<^sub>p j := LoadCode.Waypoint_struct_C.nextwaypoint_C_update (\<lambda> _. w) (heap_Waypoint_struct_C s (wsp +\<^sub>p j))]"
  sorry
    
lemma ac_bug_number_fetch[simp]:"s[wsp +\<^sub>p (uint n - 1)]\<rightarrow>number = number_C (heap_Waypoint_struct_C s (wsp +\<^sub>p (uint n - 1)))"
  sorry
 
(*    
lemma aux:
  assumes asm1:"0 < n"
  and asm2:"\<forall>s v j. j < unat (n::word16) \<longrightarrow> P s[(wsp::Waypoint_struct_C ptr) +\<^sub>p int j := v] = P s"
  and asm3:"P s"
  shows "P (LoadCode.MissionCommandUtils.update_Waypoint_struct s (wsp +\<^sub>p (uint n - 1)) w)"
proof -
  have y1:"unat (n - 1) < unat n" using asm1 measure_unat by force
  then have y2:"P s[wsp +\<^sub>p int (unat n - 1) := w]" using asm3 asm1 asm2 unat_minus_one word_neq_0_conv by fastforce
  then have "int (unat n - 1) = uint n - 1" 
    by (metis (no_types, hide_lams) cancel_comm_monoid_add_class.diff_cancel nat_less_cases' not_less of_nat_1 of_nat_diff of_nat_less_iff semiring_1_class.of_nat_0 uint_nat uint_nonnegative y1)      
  thus ?thesis using y2 by auto
qed
*)  
lemma nextwp_update_rewrite[simp]:"nextwaypoint_C_update (\<lambda>_. get_waypoint_number s[wsp +\<^sub>p j]) s[wsp +\<^sub>p j] 
              = nextwp_update s[wsp +\<^sub>p j] (get_waypoint_number s[wsp +\<^sub>p j])"
  sorry
  
lemma aux2:"              0 < n \<Longrightarrow>
              is_valid_MissionCommand s mcp \<Longrightarrow>
              Some win = waypoints_window (lift_waypoints s mcp (unat (get_waypoints_length s mcp))) i (unat n) 
\<Longrightarrow> nextwp_update sa[wsp +\<^sub>p (uint n - 1)] (get_waypoint_number sa[wsp +\<^sub>p (uint n - 1)]) = win ! j"    
  sorry

lemma aux3:" 0 < (n::word16) \<Longrightarrow> INT_MIN < uint n"
  sorry

lemma aux4:"uint (n::word16) \<le> 2147483648"
  sorry

lemma aux5:"-2147483648 < uint (n::word16) "
  sorry
    
lemma aux6:"0 < n \<Longrightarrow> \<forall>k<unat n. is_valid_Waypoint_struct_C sa (wsp +\<^sub>p int k) \<Longrightarrow> is_valid_Waypoint_struct_C sa (wsp +\<^sub>p (uint n - 1))"
  by (metis One_nat_def Suc_diff_1 le_less lessI neq0_conv of_nat_1 of_nat_diff uint_nat unat_0 word_less_nat_alt zero_less_diff)
    
lemma MCWaypointSubSequence_to_funspec:
"(\<forall> s v j. j < unat n \<longrightarrow> P (LoadCode.MissionCommandUtils.update_Waypoint_struct s (wsp +\<^sub>p j) v) = P s) \<Longrightarrow>
  \<lbrace>\<lambda> (s::lifted_globals). 
  n > 0
  \<and> is_valid_MissionCommand s mcp
  \<and> ws = lift_waypoints s mcp (unat (get_waypoints_length s mcp))
  \<and> Some win = waypoints_window ws i (unat n)
  \<and> is_valid_Waypoint_struct_C s wsp
  \<and> (\<forall> j. j < unat n \<longrightarrow> is_valid_Waypoint_struct_C s (wsp +\<^sub>p j))
  \<and> P s \<rbrace>
  LoadCode.MissionCommandUtils.MCWaypointSubSequence' mcp i n wsp 
\<lbrace> \<lambda> r s. 
  P s 
  \<and> (\<forall> j. j < unat n \<longrightarrow> heap_Waypoint_struct_C s (wsp +\<^sub>p j) = win ! j) \<rbrace>!"
  apply (rule validNF_assume_pre)
  apply (unfold LoadCode.MissionCommandUtils.MCWaypointSubSequence'_def)
  apply (subst whileLoop_add_inv[
        where I="\<lambda>(j, idit) s. 
  j \<le> n
  \<and> is_valid_MissionCommand s mcp
  \<and> (\<exists> win'. Some win' = waypoints_window ws i (unat j) \<and> prefix win' win)
  \<and> is_valid_Waypoint_struct_C s wsp
  \<and> (\<forall> k. k < unat j \<longrightarrow> is_valid_Waypoint_struct_C s (wsp +\<^sub>p k))
  \<and> P s" 
          and M="\<lambda>((i, idit),s).  unat n - unat i"],clarsimp)

      apply (rule validNF_bind[where B="\<lambda> (j,idit) s. P s 
  \<and> j = n
  \<and> is_valid_Waypoint_struct_C s wsp
  \<and> (\<forall> k. k < unat n \<longrightarrow> is_valid_Waypoint_struct_C s (wsp +\<^sub>p k))
  \<and> (\<forall> j. j < unat n \<longrightarrow> heap_Waypoint_struct_C s (wsp +\<^sub>p j) = win ! j)"])
   apply wp
   apply (simp add: Product_Type.prod.case_eq_if)
   sorry
    
  (* Trying to work forward. *)
    
end