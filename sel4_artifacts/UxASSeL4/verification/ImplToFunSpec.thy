theory ImplToFunSpec imports 
"LoadCode"
"WaypointManagerFunSpec"
begin
  
  
definition nextwp_update where
"nextwp_update w i \<equiv>   nextwaypoint_C_update (\<lambda> _. i) w"

interpretation WaypointManager number_C nextwaypoint_C nextwp_update
  apply unfold_locales
    apply (auto simp add: nextwp_update_def)
  done
 
(* Lift waypoints list in memory into a list. *)
fun lift_waypoints  where
  "lift_waypoints s wsp 0 = []"
| "lift_waypoints s wsp (Suc n) 
  = lift_waypoints s wsp n @ [heap_Waypoint_struct_C s (wsp +\<^sub>p int n)]" 

(* lift_waypoints maintains the size waypoints lifted. *)
lemma lift_waypoints_length: "ws = lift_waypoints s wsp n \<Longrightarrow> length ws = n"
  apply(induct n arbitrary: ws) by auto  

(* One can use nth to get waypoint i indirectly through lift_waypoints. *)
lemma lift_waypoints_to_get_waypoint: 
  "ws = lift_waypoints s wsp n \<Longrightarrow> \<forall> k< n.  heap_Waypoint_struct_C s (wsp +\<^sub>p k) = nth ws k"
  apply(induct n arbitrary: ws) 
   apply auto
    by (metis less_antisym lift_waypoints_length nth_append nth_append_length)
    
lemma lift_waypoint_to_take:
  "ws = lift_waypoints s wsp i \<Longrightarrow> j < i \<Longrightarrow> take j ws = lift_waypoints s wsp j"
proof(induct j arbitrary: ws)
  case 0
  then show ?case by auto
next
  case (Suc j)
  then have "take j ws = lift_waypoints s wsp j" by auto
  thus ?case using Suc
    by (metis less_asym' lift_waypoints.simps(2) lift_waypoints_length 
        lift_waypoints_to_get_waypoint not_less_eq take_Suc_conv_app_nth)
qed
  
lemma find_waypoint_extend_failure:
assumes a1:"None = find_waypoint (lift_waypoints s wsp (unat (j::16 word))) i"
and a2:"number_C (heap_Waypoint_struct_C s (wsp +\<^sub>p (uint j))) \<noteq> i"
and a3:"j < k"
shows "None = find_waypoint (lift_waypoints s wsp (unat (j + 1))) i"
proof -
  have y1:"None = find_waypoint ( lift_waypoints s wsp (unat j) 
                  @ [heap_Waypoint_struct_C s (wsp +\<^sub>p (uint j))]) i" 
    using a1 a2 find_waypoint_none_extend by blast
  then have y2:"None = find_waypoint (lift_waypoints s wsp (Suc (unat j))) i"
    by (simp add: uint_nat)
  then have y3:"(unat j) + 1 = unat (j + 1)" using a3 
    by (metis Suc_eq_plus1 add.commute less_is_non_zero_p1 unatSuc)
  thus ?thesis using Suc_eq_plus1 y2 by presburger
qed

lemma find_waypoint_failure_all_neq_number:
"ws = lift_waypoints s wsp j 
\<Longrightarrow> None = find_waypoint ws n
\<Longrightarrow> \<forall>i< j. number_C (heap_Waypoint_struct_C s (wsp +\<^sub>p (int i))) \<noteq> n"
  by (simp add: find_waypoint_failure_not_equal_all_elems lift_waypoints_length 
      lift_waypoints_to_get_waypoint)

      
lemma lift_waypoints_next_success:
assumes a1:"ws = (lift_waypoints s wsp len)"
and a2:"Some w = find_waypoint ws i"
and a3:"None = find_waypoint (take j ws)  i"
and a4:"j < len"
and a5:"i = s[wsp +\<^sub>p j]\<rightarrow>number"
shows "Some s[wsp +\<^sub>p j] = find_waypoint ws s[wsp +\<^sub>p j]\<rightarrow>number"
proof -
  have y1:"i = number_C (ws !  j)" 
    by (metis MissionCommandUtils.get_Waypoint_struct_number_def a1 a4 a5 lift_waypoints_to_get_waypoint uint_nat word_less_nat_alt)
  then have y2:"Some w = find_waypoint ws (number_C (ws ! j))" using a2 y1 by auto
  then have y3:"j < length ws" using a2 a3 not_less by fastforce
  then have "ws ! j = w" using find_waypoint_next_is_match[OF y2 _ y3] a3 y1 by auto
  thus ?thesis by (metis a1 a2 a4 a5 lift_waypoints_to_get_waypoint)
qed
     
lemma lift_waypoints_take_id:"(take len (lift_waypoints s wsp len)) = (lift_waypoints s wsp len)"
  apply(induct len)
   apply auto
    by (simp add: lift_waypoints_length)

lemma findwp_success_supp1:
"
Some w = find_waypoint (lift_waypoints s wsp len) i 
\<Longrightarrow>
None = find_waypoint (take j (lift_waypoints s wsp len)) i 
\<Longrightarrow>
j < len 
\<Longrightarrow> 
s[wsp +\<^sub>p int j]\<rightarrow>number \<noteq> i 
\<Longrightarrow> None = find_waypoint (take (Suc j) (lift_waypoints s wsp len)) i"
  by (metis MissionCommandUtils.get_Waypoint_struct_number_def find_waypoint_none_extend 
      lift_waypoints_length lift_waypoints_to_get_waypoint take_Suc_conv_app_nth)
      
lemma findwp_success_aux:
"
len \<le> USHORT_MAX 
\<Longrightarrow> 
\<lbrace> \<lambda> (s::lifted_globals).
  are_valid_Waypoints s wsp len
  \<and> (\<exists> w. Some w = find_waypoint (lift_waypoints s wsp len) i)
  \<and> P s\<rbrace>
   LoadCode.MissionCommandUtils.FindWP' wsp len i
\<lbrace> \<lambda> r s. are_valid_Waypoints s wsp len
  \<and> Some (heap_Waypoint_struct_C s r) = find_waypoint (lift_waypoints s wsp len) i 
  \<and> is_valid_Waypoint_struct_C s r 
  \<and> P s \<rbrace>!"
  apply (unfold LoadCode.MissionCommandUtils.FindWP'_def)
  apply (unfold skipE_def)
  apply wp
  apply(subst whileLoopE_add_inv
        [where 
          M = "\<lambda> (j,s). len - j"
          and I = 
            "\<lambda> j s.
            are_valid_Waypoints s wsp len 
            \<and> (\<exists> w. Some w = find_waypoint (lift_waypoints s wsp len) i)
            \<and> None = find_waypoint (take j (lift_waypoints s wsp len)) i
            \<and> P s
            \<and> j \<le> len"
        ])
  apply wp
    apply clarsimp  
    using lift_waypoints_next_success findwp_success_supp1 findwp_success_supp1 max_short_fix apply fastforce
   by (clarsimp, simp add: lift_waypoints_take_id find_waypoint_def)+    
 
lemma findwp_success[wp]: 
" 
len \<le> USHORT_MAX 
\<Longrightarrow> 
(\<forall> s. P s \<longrightarrow>  (are_valid_Waypoints s wsp len \<and> (\<exists> w. Some w = find_waypoint (lift_waypoints s wsp len) i))) 
\<Longrightarrow>
\<forall> r. 
\<lbrace>\<lambda> s::lifted_globals. 
  are_valid_Waypoints s wsp len 
  \<and> Some (heap_Waypoint_struct_C s r) = find_waypoint (lift_waypoints s wsp len) i 
  \<and> is_valid_Waypoint_struct_C s r \<and> P s\<rbrace> 
g r 
\<lbrace> Q \<rbrace>!
\<Longrightarrow>
\<lbrace> P \<rbrace> 
do x \<leftarrow> MissionCommandUtils.FindWP' wsp len i; 
        g x 
od 
\<lbrace> Q \<rbrace>!"
  apply (rule validNF_bind[where B="\<lambda> r s. are_valid_Waypoints s wsp len \<and> Some (heap_Waypoint_struct_C s r) = find_waypoint (lift_waypoints s wsp len) i \<and> is_valid_Waypoint_struct_C s r \<and> P s"])
   apply simp
  apply (rule validNF_weaken_pre[where Q="\<lambda> s. are_valid_Waypoints s wsp len \<and> (\<exists>w. Some w = find_waypoint (lift_waypoints s wsp len) i) \<and> P s"])
    apply (rule findwp_success_aux)
  by auto

lemma forward_validNF_guard_nobind[wp]:"\<lbrace> \<lambda> s. P s \<and> f s\<rbrace> g \<lbrace> Q \<rbrace>! \<Longrightarrow> (\<forall> s. P s \<longrightarrow> f s) \<Longrightarrow> \<lbrace> P \<rbrace> do guard f; g od \<lbrace> Q \<rbrace>!"
  apply (rule validNF_bind[where B = "\<lambda> r s. P s \<and> f s"])
   apply simp
  apply wp
  by auto
   
lemma forward_validNF_guard_bind:"\<lbrace> \<lambda> s. P s \<and> f s\<rbrace> g \<lbrace> Q \<rbrace>! \<Longrightarrow> (\<forall> s. P s \<longrightarrow> f s) \<Longrightarrow> \<lbrace> P \<rbrace> do  x \<leftarrow> guard f; g od \<lbrace> Q \<rbrace>!"
  apply (rule validNF_bind[where B = "\<lambda> r s. P s \<and> f s"])
   apply simp
  apply wp
  by auto    
    
lemma forward_validNF_modify[wp]:"\<lbrace> P \<rbrace> g \<lbrace> Q \<rbrace>! \<Longrightarrow> (\<forall> s. P s \<longrightarrow> P (f s)) \<Longrightarrow> \<lbrace> P \<rbrace> do x \<leftarrow> modify f; g od \<lbrace> Q \<rbrace>!"
  apply wp
  by (simp add: hoare_modifyE_var no_fail_def snd_modify validNF_def)    
    
lemma forward_validNF_whileloop_inv:" \<lbrace> P \<rbrace> whileLoop_inv c s v i m\<lbrace> \<lambda> r s. P s \<and> i r s \<and> \<not>(c r s) \<rbrace>! \<Longrightarrow> \<forall> r. \<lbrace> \<lambda> s. P s \<and> i r s \<and> \<not>(c r s) \<rbrace> g r \<lbrace> Q \<rbrace>!  \<Longrightarrow> \<lbrace> P \<rbrace> do x \<leftarrow> whileLoop_inv c s v i m; g x od \<lbrace> Q \<rbrace>!"
  apply (rule validNF_bind[where B = " \<lambda> r s. P s \<and> i r s \<and> \<not>(c r s)"])
    by auto

lemma forward_validNF_gets[wp]:"\<forall> x. \<lbrace> \<lambda> s. P s \<and> x = f s \<rbrace> g x \<lbrace> Q \<rbrace>! \<Longrightarrow> \<lbrace> P \<rbrace> do x \<leftarrow> gets f; g x od \<lbrace> Q \<rbrace>!"
  apply (rule validNF_bind[where B="\<lambda> x s. P s \<and> x = f s"])
   apply blast
  apply wp
    by auto
   
lemma are_valid_waypoints_noninter1:" ws1p +\<^sub>p len = ws2p \<Longrightarrow>  are_valid_Waypoints s ws1p len \<Longrightarrow> are_valid_Waypoints s[(ws2p::Waypoint_struct_C ptr) +\<^sub>p (k::nat) := v] ws1p len"
  apply (unfold are_valid_Waypoints_def) by auto
    
lemma are_valid_waypoints_noninter2:"ws1p +\<^sub>p len = ws2p \<Longrightarrow>  are_valid_Waypoints s[((ws2p::Waypoint_struct_C ptr) +\<^sub>p (k::nat))\<rightarrow>nextwaypoint := v] ws1p len =  are_valid_Waypoints s ws1p len"
     apply (unfold are_valid_Waypoints_def) by auto
    
lemma lift_waypoints_noninter1:"ws1p +\<^sub>p len = ws2p \<Longrightarrow>  lift_waypoints s[(ws2p::Waypoint_struct_C ptr) +\<^sub>p (k::nat) := v] ws1p len = lift_waypoints s ws1p len"
  sorry
    
lemma lift_waypoints_noninter2:"ws1p +\<^sub>p len = ws2p \<Longrightarrow>  lift_waypoints s[((ws2p::Waypoint_struct_C ptr) +\<^sub>p k)\<rightarrow>nextwaypoint := v] ws1p len =  lift_waypoints s ws1p len"
  sorry
    
lemma update_with_valid[simp]:"are_valid_Waypoints s p l \<Longrightarrow>
           is_valid_Waypoint_struct_C s r \<Longrightarrow>
           are_valid_Waypoints s[p := s[r]] p l"
  apply (unfold are_valid_Waypoints_def)
  by auto
      
lemma MCWaypointSubSequence_to_funspec:
"len_ws \<le> USHORT_MAX
\<Longrightarrow> wsp +\<^sub>p len_ws = ws_winp
\<Longrightarrow> waypoints_wf ws
\<Longrightarrow> Some win = waypoints_window ws i  len_ws_win
\<Longrightarrow> len_ws_win \<le> len_ws 
\<Longrightarrow> 0<len_ws
\<Longrightarrow> 0<len_ws_win
\<Longrightarrow> \<lbrace>\<lambda> (s::lifted_globals). 
  are_valid_Waypoints s ws_winp len_ws_win
  \<and>  are_valid_Waypoints s wsp len_ws
  \<and> ws = lift_waypoints s wsp len_ws\<rbrace>
  LoadCode.MissionCommandUtils.MCWaypointSubSequence' wsp len_ws i len_ws_win ws_winp
\<lbrace> \<lambda> r s. 
 (\<forall> j. j <  len_ws_win \<longrightarrow> heap_Waypoint_struct_C s (ws_winp +\<^sub>p j) = win ! j) \<rbrace>!"
  apply (unfold LoadCode.MissionCommandUtils.MCWaypointSubSequence'_def)
      apply(subst whileLoop_add_inv
        [where 
          M = "\<lambda> ((j,nid),s). len_ws_win - j"
          and I = 
            "\<lambda> (j,nid) s.
  are_valid_Waypoints s ws_winp len_ws_win
  \<and>  are_valid_Waypoints s wsp len_ws
  \<and> ws = lift_waypoints s wsp len_ws
            \<and> j < len_ws_win
\<and> (j = 0 \<longrightarrow> nid = sint i)
\<and> (0 < j \<longrightarrow> nid = sint (nextwaypoint_C (win ! (j - 1))))
\<and>  (\<forall> k. k < j \<longrightarrow> heap_Waypoint_struct_C s (ws_winp +\<^sub>p k) = win ! k)
"
        ])
  apply clarsimp
     apply (rule forward_validNF_whileloop_inv)
    apply (wp_once, clarsimp)
     apply(rule forward_validNF_guard_nobind forward_validNF_gets forward_validNF_guard_bind forward_validNF_modify findwp_success | clarsimp)+
  defer
    defer
      apply (wp | clarsimp )+ 
    
end