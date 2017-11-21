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
and a5:"i = number_C (heap_Waypoint_struct_C s (wsp +\<^sub>p j))"
shows "Some (heap_Waypoint_struct_C s (wsp +\<^sub>p j)) = find_waypoint ws (number_C (heap_Waypoint_struct_C s (wsp +\<^sub>p j)))"
proof -
  have y1:"i = number_C (ws !  j)" 
    by (metis a1 a4 a5 lift_waypoints_to_get_waypoint)
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
 (number_C (heap_Waypoint_struct_C s(wsp +\<^sub>p int j))) \<noteq> i 
\<Longrightarrow> None = find_waypoint (take (Suc j) (lift_waypoints s wsp len)) i"
  by (metis find_waypoint_none_extend 
      lift_waypoints_length lift_waypoints_to_get_waypoint take_Suc_conv_app_nth)
      
lemma findwp_success_aux[wp]:
"
\<lbrace> \<lambda> (s::lifted_globals).
  len \<le> USHORT_MAX 
  \<and> are_valid_Waypoints s wsp len
  \<and> (\<exists> w. Some w = find_waypoint (lift_waypoints s wsp len) i)
  \<and> P s\<rbrace>
   LoadCode.MissionCommandUtils.FindWP' wsp len i
\<lbrace> \<lambda> r s. are_valid_Waypoints s wsp len
  \<and> Some (heap_Waypoint_struct_C s r) = find_waypoint (lift_waypoints s wsp len) i 
  \<and> is_valid_Waypoint_struct_C s r 
  \<and> P s \<rbrace>!"
  apply (rule validNF_assume_pre)
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
\<forall> r. 
\<lbrace> \<lambda> s.  are_valid_Waypoints s wsp len
  \<and> Some (heap_Waypoint_struct_C s r) = find_waypoint (lift_waypoints s wsp len) i 
  \<and> is_valid_Waypoint_struct_C s r 
  \<and> P s\<rbrace> 
g r 
\<lbrace> Q \<rbrace>!
\<Longrightarrow>
(\<forall> s. P s \<longrightarrow>  len \<le> USHORT_MAX  \<and> are_valid_Waypoints s wsp len \<and> (\<exists> w. Some w = find_waypoint (lift_waypoints s wsp len) i)) 
\<Longrightarrow>
\<lbrace> P \<rbrace> 
do x \<leftarrow> MissionCommandUtils.FindWP' wsp len i; 
        g x 
od 
\<lbrace> Q \<rbrace>!"    
  apply (rule validNF_bind[where B="\<lambda> r s. are_valid_Waypoints s wsp len \<and> Some (heap_Waypoint_struct_C s r) = find_waypoint (lift_waypoints s wsp len) i \<and> is_valid_Waypoint_struct_C s r \<and> P s"])
   apply simp
     apply (rule validNF_weaken_pre)
   apply (rule validNF_weaken_pre[where Q="\<lambda> s. len \<le> USHORT_MAX  \<and> are_valid_Waypoints s wsp len \<and> (\<exists> w. Some w = find_waypoint (lift_waypoints s wsp len) i) \<and> P s"])
   apply (rule findwp_success_aux)
  by blast+
    
lemma validNF_guard_bind[wp]:"\<lbrace>\<lambda> s. A s \<and> f s\<rbrace> g () \<lbrace> B \<rbrace>! \<Longrightarrow> \<forall> s. A s \<longrightarrow> f s \<Longrightarrow> \<lbrace>A\<rbrace> guard f >>= g \<lbrace>B\<rbrace>!"
  apply (rule validNF_bind[where B="\<lambda> _ s. A s \<and> f s"])
  by (wp | auto)+
    
lemma validNF_whileloop_inv[wp]:"\<forall> r. \<lbrace> \<lambda> s. P s \<and> i r s \<and> \<not> (c r s) \<rbrace> g r \<lbrace> Q \<rbrace>!
\<Longrightarrow> \<lbrace> P \<rbrace> whileLoop_inv c s v i m \<lbrace> \<lambda> r s. P s \<and> i r s \<and> \<not>(c r s) \<rbrace>!  
\<Longrightarrow> \<lbrace> P \<rbrace> do x \<leftarrow> whileLoop_inv c s v i m; g x od \<lbrace> Q \<rbrace>!"
  apply (rule validNF_bind[where B = "\<lambda> r s. P s \<and> i r s \<and> \<not>(c r s)"])
  by auto
    
lemma validNF_modify[wp]:"\<forall> s'. \<lbrace> \<lambda> s. P s \<and> s = f s' \<rbrace> g \<lbrace> Q \<rbrace>! \<Longrightarrow> \<lbrace> \<lambda> s. P s\<rbrace> do x \<leftarrow> modify f; g od \<lbrace> Q \<rbrace>!"
  sorry
    
lemma forward_validNF_gets[wp]:"\<forall> x. \<lbrace> \<lambda> s. P s \<and> x = f s \<rbrace> g x \<lbrace> Q \<rbrace>! \<Longrightarrow> \<lbrace> P \<rbrace> do x \<leftarrow> gets f; g x od \<lbrace> Q \<rbrace>!"
  apply (rule validNF_bind[where B="\<lambda> x s. P s \<and> x = f s"])
   apply blast
  apply wp
    by auto

lemma validNF_nobind[wp]:"\<lbrace>B\<rbrace> g \<lbrace>C\<rbrace>! \<Longrightarrow> \<lbrace>A\<rbrace> f \<lbrace>\<lambda>r. B\<rbrace>! \<Longrightarrow> \<lbrace>A\<rbrace> do f;
      g
  od \<lbrace>C \<rbrace>!"  
  by wp      
      
lemma are_valid_waypoints_noninter[simp]:"are_valid_Waypoints (heap_Waypoint_struct_C_update f s) p2 len = are_valid_Waypoints s p2 len"
  apply (unfold are_valid_Waypoints_def) by auto

lemma rename8[simp]:"x \<noteq> y \<Longrightarrow> heap_Waypoint_struct_C (heap_Waypoint_struct_C_update (\<lambda>b c. if c = x then v else b c) s') y = heap_Waypoint_struct_C s' y"
  by auto
    
(* TODO: How do I prove this *)
lemma base_Waypoint_struct_C_ptr_ineq:"(p::Waypoint_struct_C ptr) +\<^sub>p (1::nat) \<noteq> p" 
  sorry
(* TODO: How do I prove this *)
lemma general_Waypoint_struct_C_ptr_ineq:"0<(x::nat)  \<Longrightarrow> (p::Waypoint_struct_C ptr) +\<^sub>p  x  \<noteq> p "   
  sorry
    
lemma MCWaypointSubSequence_to_funspec_supp1:
assumes a2:"Some win  = waypoints_window_aux ws i len"
and a3:"int a < int len"
and a4:"a = 0 \<longrightarrow> b = sint i"
and a5:"0 < a \<longrightarrow> b = sint (nextwaypoint_C (win ! (a - Suc 0)))"
shows "\<exists>w. Some w = find_waypoint ws (of_int b)"
proof -
  have "a = 0 \<or> 0 < a" by auto
  thus ?thesis
  proof 
    assume "a = 0"
    thus ?thesis by (metis a2 a4 of_int_sint waypoint_window_aux_find_waypoint_hd)
  next
    assume "0 < a"
    thus ?thesis using a2 a3 a5 waypoint_window_aux_nextwp by force
  qed
qed
    
lemma MCWaypointSubSequence_to_funspec_supp2:
assumes a1:"Some win = waypoints_window_aux (lift_waypoints s' wsp len_ws) i len_ws_win" 
and a2:"Some (heap_Waypoint_struct_C s' r) = find_waypoint (lift_waypoints s' wsp len_ws) (of_int b)"
and a3:"a = 0 \<longrightarrow> b = sint i"
and a4:"0 < a \<longrightarrow> b = sint (nextwaypoint_C (win ! (a - Suc 0)))"
and a5:"a < len_ws_win"
shows "nextwaypoint_C (heap_Waypoint_struct_C s' r) = nextwaypoint_C (win ! a)"
proof -
  have y1:"(\<forall>j<len_ws_win. 0 < j \<longrightarrow> Some (win ! j) = find_waypoint (lift_waypoints s' wsp len_ws) (nextwaypoint_C (win ! (j - 1))))" and 
  y2:"\<forall> j<len_ws_win. j = 0 \<longrightarrow> Some (win ! j) = find_waypoint (lift_waypoints s' wsp len_ws) i" using waypoint_window_aux_nextwp[OF sym[OF a1]] by auto
  have "a = 0 \<or> 0 < a" by auto
  thus ?thesis
  proof
    assume "a = 0"
    thus ?thesis by (metis a5 of_int_sint option.inject y2 a3 a2)
  next 
    assume "0 < a"
    thus ?thesis using y1 a4 a2 a5 by (metis One_nat_def of_int_sint option.inject)
   qed
qed

lemma MCWaypointSubSequence_to_funspec_supp3:
assumes a4:"Some win =
                waypoints_window_aux
                 (lift_waypoints (heap_Waypoint_struct_C_update (\<lambda>b c. if c = wsp +\<^sub>p int len_ws +\<^sub>p int a then heap_Waypoint_struct_C s' r else b c) s') wsp len_ws) i
                 len_ws_win"
and a8:"Some (heap_Waypoint_struct_C s' r) =
                find_waypoint (lift_waypoints (heap_Waypoint_struct_C_update (\<lambda>b c. if c = wsp +\<^sub>p int len_ws +\<^sub>p int a then heap_Waypoint_struct_C s' r else b c) s') wsp len_ws)
                 (of_int b)"
and a12:"a = 0 \<longrightarrow> b = sint i"
and a13:"0 < a \<longrightarrow> b = sint (nextwaypoint_C (win ! (a - Suc 0)))"
and a15:"a < len_ws_win"
shows "nextwaypoint_C (heap_Waypoint_struct_C s' r) = nextwaypoint_C (win ! a)"
proof -
  have "a = 0 \<or> 0 < a" by auto
  thus ?thesis
  proof
    assume "a = 0"
    thus ?thesis
      by (metis (no_types, lifting) a12 a4 a8 hd_conv_nth of_int_sint option.inject waypoint_window_aux_find_waypoint_hd waypoint_window_aux_success_len_nonempty)
  next
    assume "0 < a"
    thus ?thesis by (metis (no_types, lifting) One_nat_def a13 a15 a4 a8 of_int_sint option.inject waypoint_window_aux_nextwp)
  qed
qed

lemma MCWaypointSubSequence_to_funspec_supp4_old:
assumes a4:"Some win =
       waypoints_window_aux (lift_waypoints (heap_Waypoint_struct_C_update (\<lambda>b c. if c = wsp +\<^sub>p int len_ws +\<^sub>p int a then heap_Waypoint_struct_C s' r else b c) s') wsp len_ws) i
        len_ws_win"
and a8:"Some (heap_Waypoint_struct_C s' r) =
       find_waypoint (lift_waypoints (heap_Waypoint_struct_C_update (\<lambda>b c. if c = wsp +\<^sub>p int len_ws +\<^sub>p int a then heap_Waypoint_struct_C s' r else b c) s') wsp len_ws)
        (of_int b)"
and a12:"a = 0 \<longrightarrow> b = sint i"
and a13:"0 < a \<longrightarrow> b = sint (nextwaypoint_C (win ! (a - Suc 0)))"
and a14:"\<forall>k\<le>a - Suc 0.
          0 < a \<longrightarrow>
          (if wsp +\<^sub>p int len_ws +\<^sub>p int k = wsp +\<^sub>p int len_ws +\<^sub>p int a then heap_Waypoint_struct_C s' r else heap_Waypoint_struct_C s' (wsp +\<^sub>p int len_ws +\<^sub>p int k)) =
          win ! k"
and a15:"a < len_ws_win"
and a16:"wsp +\<^sub>p int len_ws +\<^sub>p int k = wsp +\<^sub>p int len_ws +\<^sub>p int a"
and a17:"k \<le> a"
shows "heap_Waypoint_struct_C s' r = win ! k"
proof -
  have "k = a \<or> k < a" using a17 by auto
  thus ?thesis
  proof
    assume y1:"k = a"
   thus ?thesis by (metis (no_types, lifting) One_nat_def a12 a13 a15 a4 a8 not_gr_zero of_int_sint option.inject waypoint_window_aux_nextwp)          
  next 
    assume y1:"k < a"
    then have "k \<le> a - Suc 0" by auto
    thus ?thesis using a14 a16 y1 by auto
  qed
qed
  
lemma MCWaypointSubSequence_to_funspec_supp4:"len_ws \<le> USHORT_MAX \<Longrightarrow>
       ws_winp = wsp +\<^sub>p int len_ws \<Longrightarrow>
       Some win = waypoints_window_aux (lift_waypoints s' wsp len_ws) i len_ws_win \<Longrightarrow>
       len_ws_win < len_ws \<Longrightarrow>
       \<forall>s v a. a < len_ws_win \<longrightarrow>
               lift_waypoints (heap_Waypoint_struct_C_update (\<lambda>b c. if c = wsp +\<^sub>p int len_ws +\<^sub>p int a then v else b c) s) wsp len_ws = lift_waypoints s wsp len_ws \<Longrightarrow>
       are_valid_Waypoints s' wsp len_ws \<Longrightarrow>
       Some (heap_Waypoint_struct_C s' r) = find_waypoint (lift_waypoints s' wsp len_ws) (of_int b) \<Longrightarrow>
       is_valid_Waypoint_struct_C s' r \<Longrightarrow>
       are_valid_Waypoints s' (wsp +\<^sub>p int len_ws) len_ws_win \<Longrightarrow>
       ws = lift_waypoints s' wsp len_ws \<Longrightarrow>
       a = 0 \<longrightarrow> b = sint i \<Longrightarrow>
       0 < a \<longrightarrow> b = sint (nextwaypoint_C (win ! (a - Suc 0))) \<Longrightarrow>
       \<forall>k\<le>a - Suc 0.
          0 < a \<longrightarrow>
          (if wsp +\<^sub>p int len_ws +\<^sub>p int k = wsp +\<^sub>p int len_ws +\<^sub>p int a then heap_Waypoint_struct_C s' r else heap_Waypoint_struct_C s' (wsp +\<^sub>p int len_ws +\<^sub>p int k)) =
          win ! k \<Longrightarrow>
       a < len_ws_win \<Longrightarrow> wsp +\<^sub>p int len_ws +\<^sub>p int k = wsp +\<^sub>p int len_ws +\<^sub>p int a \<Longrightarrow> k \<le> a \<Longrightarrow> heap_Waypoint_struct_C s' r = win ! k"  
  sorry

lemma MCWaypointSubSequence_to_funspec_supp5:
assumes a14:"\<forall>k\<le>a - Suc 0.
          0 < a \<longrightarrow>
          (if wsp +\<^sub>p int len_ws +\<^sub>p int k = wsp +\<^sub>p int len_ws +\<^sub>p int a then heap_Waypoint_struct_C s' r else heap_Waypoint_struct_C s' (wsp +\<^sub>p int len_ws +\<^sub>p int k)) =
          win ! k"
and a16:"wsp +\<^sub>p int len_ws +\<^sub>p int k \<noteq> wsp +\<^sub>p int len_ws +\<^sub>p int a"
and a17:"k \<le> a"
shows "heap_Waypoint_struct_C s' (wsp +\<^sub>p int len_ws +\<^sub>p int k) = win ! k"
proof -
  have "k = a \<or> k < a" using a17 by auto
  thus ?thesis
  proof
    assume "k = a"
    thus ?thesis using a16 by auto
  next
    assume "k < a"
    then have "k \<le> a - Suc 0" by auto
    thus ?thesis using a14 a16 by auto
  qed
qed
  
lemma lift_lift_waypoint_agnostic_prop:
"a < len_ws_win
\<Longrightarrow> \<forall>(s::lifted_globals) v a. a < len_ws_win \<longrightarrow>
                        lift_waypoints (heap_Waypoint_struct_C_update (\<lambda>b c. if c = wsp +\<^sub>p int len_ws +\<^sub>p int a then v else b c) s) wsp len_ws = lift_waypoints s wsp len_ws
\<Longrightarrow>
lift_waypoints (heap_Waypoint_struct_C_update (\<lambda>b c. if c = wsp +\<^sub>p int len_ws +\<^sub>p int a then v else b c) (s::lifted_globals)) wsp len_ws = lift_waypoints s wsp len_ws"
by auto

(*
theorem "size_td (typ_info_t TYPE(Waypoint_struct_C)) = x"
  apply simp

 *)  
lemma FillWaypoint_to_funspec:
"len_ws \<le> USHORT_MAX
\<Longrightarrow> ws_winp = wsp +\<^sub>p len_ws
\<Longrightarrow> Some win = waypoints_window_aux ws i len_ws_win
\<Longrightarrow> len_ws_win < len_ws 
\<Longrightarrow> 0<len_ws_win
\<Longrightarrow> (\<forall> (s::lifted_globals) v a. a < len_ws_win  \<longrightarrow> lift_waypoints (heap_Waypoint_struct_C_update (\<lambda>b c. if c = ws_winp +\<^sub>p int a then v else b c) s) wsp len_ws = lift_waypoints s wsp len_ws)
\<Longrightarrow> \<lbrace>\<lambda> (s::lifted_globals).
  are_valid_Waypoints s ws_winp len_ws_win
  \<and> are_valid_Waypoints s wsp len_ws
  \<and> ws = lift_waypoints s wsp len_ws \<rbrace>
  LoadCode.MissionCommandUtils.FillWindow' wsp len_ws i len_ws_win ws_winp
\<lbrace> \<lambda> r s. 
  are_valid_Waypoints s ws_winp len_ws_win
  \<and> are_valid_Waypoints s wsp len_ws
  \<and> ws = lift_waypoints s wsp len_ws
  \<and> (\<forall> j. j <  len_ws_win \<longrightarrow> heap_Waypoint_struct_C s (ws_winp +\<^sub>p j) = win ! j) \<rbrace>!"
  apply (unfold LoadCode.MissionCommandUtils.FillWindow'_def)
      apply(subst whileLoop_add_inv
        [where 
          M = "\<lambda> ((j,nid),s). len_ws_win - j"
          and I = 
            "\<lambda> (j,nid) s.
  are_valid_Waypoints s ws_winp len_ws_win
  \<and>  are_valid_Waypoints s wsp len_ws
  \<and> ws = lift_waypoints s wsp len_ws
  \<and> j \<le> len_ws_win
\<and> (j = 0 \<longrightarrow> nid = sint i)
\<and> (0 < j \<longrightarrow> nid = sint (nextwaypoint_C (win ! (j - 1))))
\<and> (\<forall> k \<le> j - 1. 0 < j \<longrightarrow> heap_Waypoint_struct_C s (ws_winp +\<^sub>p k) = win ! k)
" ])
  apply ( assumption 
      | clarsimp  
      | wp_once 
      | simp add: lift_lift_waypoint_agnostic_prop 
                  MCWaypointSubSequence_to_funspec_supp2)+
         apply rule+
    
           apply (rule MCWaypointSubSequence_to_funspec_supp4)   
            apply(assumption | clarsimp)+
          apply(rule MCWaypointSubSequence_to_funspec_supp5)
     apply(assumption | clarsimp)+
                      apply (assumption | simp add: MCWaypointSubSequence_to_funspec_supp1 | clarsimp)+
  done
    
lemma foo:"
Some win' = waypoints_window_aux ws i len_ws_win \<Longrightarrow>
\<lbrace>\<lambda> (s::lifted_globals).
  are_valid_Waypoints s ws_winp len_ws_win
  \<and> are_valid_Waypoints s wsp len_ws
  \<and> ws = lift_waypoints s wsp len_ws
 \<and> (\<forall> j. j <  len_ws_win \<longrightarrow> heap_Waypoint_struct_C s (ws_winp +\<^sub>p j) = win' ! j)
\<rbrace>
  LoadCode.MissionCommandUtils.GroomWindow' len_ws_win ws_winp
\<lbrace> \<lambda> r s. 
  are_valid_Waypoints s ws_winp len_ws_win
  \<and> are_valid_Waypoints s wsp len_ws
  \<and> ws = lift_waypoints s wsp len_ws
  \<and> (\<exists> win. Some win = waypoints_window ws i len_ws_win
    \<and> (\<forall> j. j <  len_ws_win \<longrightarrow> heap_Waypoint_struct_C s (ws_winp +\<^sub>p j) = win ! j)) \<rbrace>!"
  sorry

lemma FillAndGroomWaypoint_to_funspec:
"len_ws \<le> USHORT_MAX
\<Longrightarrow> ws_winp = wsp +\<^sub>p len_ws
\<Longrightarrow> waypoints_wf ws
\<Longrightarrow> Some win' = waypoints_window_aux ws i  len_ws_win
\<Longrightarrow> len_ws_win < len_ws 
\<Longrightarrow> 0<len_ws_win
\<Longrightarrow> (\<forall> (s::lifted_globals) v a. a < len_ws_win  \<longrightarrow> lift_waypoints (heap_Waypoint_struct_C_update (\<lambda>b c. if c = ws_winp +\<^sub>p int a then v else b c) s) wsp len_ws = lift_waypoints s wsp len_ws)
\<Longrightarrow> \<lbrace>\<lambda> (s::lifted_globals).
  are_valid_Waypoints s ws_winp len_ws_win
  \<and> are_valid_Waypoints s wsp len_ws
  \<and> ws = lift_waypoints s wsp len_ws \<rbrace>
  LoadCode.MissionCommandUtils.FillAndGroomWindow' wsp len_ws i len_ws_win ws_winp
\<lbrace> \<lambda> r s. 
  are_valid_Waypoints s ws_winp len_ws_win
  \<and> are_valid_Waypoints s wsp len_ws
  \<and> ws = lift_waypoints s wsp len_ws
  \<and> (\<exists> win. Some win = waypoints_window ws i len_ws_win
    \<and> (\<forall> j. j <  len_ws_win \<longrightarrow> heap_Waypoint_struct_C s (ws_winp +\<^sub>p j) = win ! j)) \<rbrace>!"
  apply (unfold LoadCode.MissionCommandUtils.FillAndGroomWindow'_def)
  apply (rule validNF_nobind[where B="\<lambda> s. 
  are_valid_Waypoints s ws_winp len_ws_win
  \<and> are_valid_Waypoints s wsp len_ws
  \<and> ws = lift_waypoints s wsp len_ws
  \<and> (\<forall> j. j <  len_ws_win \<longrightarrow> heap_Waypoint_struct_C s (ws_winp +\<^sub>p j) = win' ! j)"])
   apply (rule foo)
        apply (clarsimp | assumption )+ 
   apply (rule FillWaypoint_to_funspec)
       apply (clarsimp | assumption )+
done
    
end