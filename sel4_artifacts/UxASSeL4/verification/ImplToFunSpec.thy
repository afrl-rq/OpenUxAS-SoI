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
   LoadCode.WaypointManagerUtils.FindWaypoint' wsp len i
\<lbrace> \<lambda> r s. are_valid_Waypoints s wsp len
  \<and> Some (heap_Waypoint_struct_C s r) = find_waypoint (lift_waypoints s wsp len) i
  \<and> is_valid_Waypoint_struct_C s r
  \<and> r \<noteq> NULL 
  \<and> P s \<rbrace>!"
 apply (rule validNF_assume_pre)
 apply (unfold LoadCode.WaypointManagerUtils.FindWaypoint'_def)
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
   apply auto
      apply (metis lift_waypoints_next_success option.inject)
     using are_valid_Waypoints_def apply blast
    apply (metis findwp_success_supp1)
   using max_short_fix  apply fastforce
  apply (simp add: lift_waypoints_take_id)
   by (metis append_is_Nil_conv find_waypoint_success_construction option.exhaust)
    
lemma findwp_success[wp]: 
" 
\<forall> r. 
\<lbrace> \<lambda> s.  are_valid_Waypoints s wsp len
  \<and> Some (heap_Waypoint_struct_C s r) = find_waypoint (lift_waypoints s wsp len) i 
  \<and> is_valid_Waypoint_struct_C s r 
  \<and> r \<noteq> NULL
  \<and> P s\<rbrace> 
g r 
\<lbrace> Q \<rbrace>!
\<Longrightarrow> (\<forall> s. P s \<longrightarrow>  len \<le> USHORT_MAX  \<and> are_valid_Waypoints s wsp len \<and> (\<exists> w. Some w = find_waypoint (lift_waypoints s wsp len) i))
\<Longrightarrow> \<lbrace> P \<rbrace> 
do x \<leftarrow> WaypointManagerUtils.FindWaypoint' wsp len i; 
        g x 
od 
\<lbrace> Q \<rbrace>!"
  apply (rule validNF_bind[where B="\<lambda> r s. are_valid_Waypoints s wsp len \<and> Some (heap_Waypoint_struct_C s r) = find_waypoint (lift_waypoints s wsp len) i \<and> is_valid_Waypoint_struct_C s r \<and> r \<noteq> NULL \<and> P s"])
    apply simp 
    apply (rule validNF_weaken_pre)
   apply (rule validNF_weaken_pre[where Q="\<lambda> s. len \<le> USHORT_MAX  \<and> are_valid_Waypoints s wsp len \<and> (\<exists> w. Some w = find_waypoint (lift_waypoints s wsp len) i) \<and> P s"])
   apply (rule findwp_success_aux)
  by blast+
    
lemma validNF_guard_bind[wp]:"\<lbrace>\<lambda> s. A s \<and> f s\<rbrace> g () \<lbrace> B \<rbrace>! \<Longrightarrow> \<forall> s. A s \<longrightarrow> f s \<Longrightarrow> \<lbrace>A\<rbrace> guard f >>= g \<lbrace>B\<rbrace>!"
  apply (rule validNF_bind[where B="\<lambda> _ s. A s \<and> f s"])
  by (wp | auto)+
    
(* Sledgehammer heads off down some rabbit hole. *) 
lemma validNF_modify_supp1:"\<forall> s'. \<lbrace>P s'\<rbrace> g \<lbrace>Q\<rbrace>! \<Longrightarrow> \<lbrace>\<lambda>s. \<exists> s'. P s' s\<rbrace> g \<lbrace>Q\<rbrace>!"
proof -
  assume a1:"\<forall> s'. \<lbrace>P s'\<rbrace> g \<lbrace>Q\<rbrace>!"
  then have "\<exists> x. (\<forall>s. P x s \<longrightarrow> (\<forall>(r', s')\<in>fst (g s). Q r' s') \<and> \<not> snd (g s))"  by (simp add: validNF_alt_def)
  then have "(\<forall>s. \<exists>x. P x s \<longrightarrow> (\<forall>(r', s')\<in>fst (g s). Q r' s') \<and> \<not> snd (g s))" by meson
  then have "(\<forall>s. (\<exists>x. P x s) \<longrightarrow> (\<forall>(r', s')\<in>fst (g s). Q r' s') \<and> \<not> snd (g s))" by (meson a1 validNF_alt_def)      
  then have "\<lbrace>\<lambda>s. \<exists>x. P x s\<rbrace> g \<lbrace>Q\<rbrace>!"  using sym[OF validNF_alt_def[where P="\<lambda> s. \<exists> x. P x s" and m=g and Q=Q]] by auto
  thus ?thesis by auto
qed

lemma validNF_modify_supp2:" \<forall>s'. \<lbrace>\<lambda>s. P s' \<and> s = f s'\<rbrace> g \<lbrace>Q\<rbrace>! \<Longrightarrow> \<lbrace>P\<rbrace> modify f \<lbrace>\<lambda>_ s. \<exists>s'. P s' \<and> s = f s'\<rbrace>!"
  apply wp by auto
    
lemma validNF_modify[wp]:"\<forall> s'. \<lbrace> \<lambda> s. P s' \<and> s = f s' \<rbrace> g \<lbrace> Q \<rbrace>! \<Longrightarrow> \<lbrace> P \<rbrace> do x \<leftarrow> modify f; g od \<lbrace> Q \<rbrace>!"   
  apply (rule validNF_bind[where B="\<lambda> _ s. \<exists> s'. P s' \<and> s = f s'"])
  apply (rule validNF_modify_supp1) 
   apply simp
  apply (rule validNF_modify_supp2)
  apply simp
  done

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

(*
(* TODO: How do I prove this *)
lemma base_Waypoint_struct_C_ptr_ineq:"(p::Waypoint_struct_C ptr) +\<^sub>p (1::nat) \<noteq> p" 
  
(* TODO: How do I prove this *)
lemma general_Waypoint_struct_C_ptr_ineq:"0<(x::nat)  \<Longrightarrow> (p::Waypoint_struct_C ptr) +\<^sub>p  x  \<noteq> p "   
 

theorem "size_td (typ_info_t TYPE(Waypoint_struct_C)) = x"
  apply simp

 *)  
lemma MCWaypointSubSequence_to_funspec_supp1:
assumes a2:"Some win = waypoints_window_aux (lift_waypoints s wsp len_ws) i len_ws_win"
and a8:"a = 0 \<longrightarrow> b = sint i"
and a9:"0 < a \<longrightarrow> b = sint (nextwaypoint_C (win ! (a - Suc 0)))"
and a11:"a < len_ws_win" 
shows "Some (win ! a) = find_waypoint (lift_waypoints s wsp len_ws) (of_int b)"
proof - 
  have "a = 0 \<or> 0 < a" by auto
  thus ?thesis
  proof
    assume "a = 0"
    thus ?thesis using a11 a2 a8 waypoint_window_aux_nextwp by auto
  next
    assume "0 < a"
    thus ?thesis using a11 a2 a9 waypoint_window_aux_nextwp by auto
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

lemma MCWaypointSubSequence_to_funspec_supp4:
assumes a1:"len_ws \<le> USHORT_MAX"
and a2:"Some win = waypoints_window_aux (lift_waypoints s' wsp len_ws) i len_ws_win"
and a3:"len_ws_win \<le> len_ws"
and a6:"Some (heap_Waypoint_struct_C s' r) = find_waypoint (lift_waypoints s' wsp len_ws) (of_int b)"
and a10:"a = 0 \<longrightarrow> b = sint i"
and a11:"0 < a \<longrightarrow> b = sint (nextwaypoint_C (win ! (a - Suc 0)))"
and a13:"a < len_ws_win"
and a14:"wsp +\<^sub>p int len_ws +\<^sub>p int k = wsp +\<^sub>p int len_ws +\<^sub>p int a"
and a15:"k \<le> a"
shows "heap_Waypoint_struct_C s' r = win ! k"  
proof -
  have y1:"a \<le> USHORT_MAX"  using a1 a13 a3 by auto 
  have y2:"k \<le> USHORT_MAX"  using a15 y1 by auto
  have y3:"a = k" using ptr_offset_equality a14 y1 y2 by fastforce
  then have " a = 0 \<or> 0 < a" by auto
  thus ?thesis
  proof 
    assume "a = 0"
    thus ?thesis
      by (metis a10 a2 a6 hd_conv_nth of_int_sint option.inject waypoint_window_aux_find_waypoint_hd waypoint_window_aux_success_len_nonempty y3)
  next
    assume "0 < a"
    thus ?thesis
      by (metis One_nat_def a11 a13 a2 a6 of_int_sint option.inject waypoint_window_aux_nextwp y3)
  qed
qed

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
                        lift_waypoints (heap_Waypoint_struct_C_update (\<lambda>b c. if c = wsp +\<^sub>p int len_ws +\<^sub>p int a then v b else b c) s) wsp len_ws = lift_waypoints s wsp len_ws
\<Longrightarrow>
lift_waypoints (heap_Waypoint_struct_C_update (\<lambda>b c. if c = wsp +\<^sub>p int len_ws +\<^sub>p int a then v b else b c) (s::lifted_globals)) wsp len_ws = lift_waypoints s wsp len_ws"
by auto
      
lemma condition_sufficient_left:"\<forall> s. Q s \<longrightarrow> P s \<Longrightarrow> \<lbrace>\<lambda> s. Q s \<and> P s\<rbrace> A \<lbrace> R \<rbrace>! \<Longrightarrow> \<lbrace>\<lambda> s. Q s\<rbrace> condition P A B \<lbrace> R \<rbrace>!"
    apply(unfold validNF_def)
  apply(unfold valid_def)
    by (metis (mono_tags) condition_true no_fail_def)
  
lemma validNF_bind_split:"\<lbrace> A \<rbrace> f >>= g \<lbrace> C \<rbrace>! \<Longrightarrow> \<exists> B. (\<lbrace> A \<rbrace> f \<lbrace> B \<rbrace>! \<and> (\<forall> r. \<lbrace> B r \<rbrace> g r \<lbrace> C \<rbrace>!))"
  apply(rule exI[where x="\<lambda> r s2. \<exists> s. A s \<and> (r,s2)\<in>fst (f s) \<and> \<not> snd (f s) \<and> (\<forall> v2 \<in> fst (g r s2). (case v2 of (r2,s3) \<Rightarrow> C r2 s3))"])
   apply (unfold bind_def validNF_def valid_def no_fail_def)
  by (clarsimp | auto | blast)+


(*  assume a1:"\<lbrace>A\<rbrace> f >>= g \<lbrace>C\<rbrace>!"
  assume a2:"\<nexists>B. \<lbrace>A\<rbrace> f \<lbrace>B\<rbrace>! \<and> (\<forall>r. \<lbrace>B r\<rbrace> g r \<lbrace>C\<rbrace>!)"
   thus ?thesis sledgehammer[z3 e spass] *)
(*  assume a1:"\<lbrace> A \<rbrace> f >>= g \<lbrace> C \<rbrace>!"
  then obtain B where y1:"\<lbrace> A \<rbrace> f \<lbrace> B \<rbrace>!" 
    by (metis no_fail_def no_fail_is_validNF_True snd_bind validNF_alt_def validNF_valid)
  then have "(\<forall> r. \<lbrace> B r \<rbrace> g r \<lbrace> C \<rbrace>!) \<or> \<not>(\<forall> r. \<lbrace> B r \<rbrace> g r \<lbrace> C \<rbrace>!)" by auto
  thus ?thesis
  proof
    assume a2:"(\<forall> r. \<lbrace> B r \<rbrace> g r \<lbrace> C \<rbrace>!)"
    thus ?thesis using y1 by auto
  next
    assume a2:"\<not>(\<forall> r. \<lbrace> B r \<rbrace> g r \<lbrace> C \<rbrace>!)"
    then obtain r where "\<not> (\<lbrace> B r\<rbrace> g r \<lbrace> C \<rbrace>!)" by auto
    then have "((\<exists> s. \<lbrace> \<lambda> s'. A s' \<and> s = s'\<rbrace> f \<lbrace> \<lambda> r' s. r' = r\<rbrace>) \<or> \<not> (\<exists> s. \<lbrace> \<lambda> s'. A s' \<and> s = s'\<rbrace> f \<lbrace> \<lambda> r' s. r' = r\<rbrace>))" by auto
    thus ?thesis
    proof
      assume "(\<exists> s. \<lbrace> \<lambda> s'. A s' \<and> s = s'\<rbrace> f \<lbrace> \<lambda> r' s. r' = r\<rbrace>)"
      then obtain s where "\<lbrace> \<lambda> s'. A s' \<and> s = s'\<rbrace> f \<lbrace> \<lambda> r' s. r' = r\<rbrace>" by auto
      then have "\<not> \<lbrace>\<lambda> s'. A s' \<and> s = s' \<rbrace> f >>= g \<lbrace> C \<rbrace>!" 
  apply
  sorry*)
    
lemma validNF_condition_tru[wp]:"\<forall> s. Q s \<longrightarrow> P s \<Longrightarrow> \<lbrace>\<lambda> s. Q s \<and> P s\<rbrace> A >>= g \<lbrace>R\<rbrace>! \<Longrightarrow> \<lbrace>\<lambda> s. Q s\<rbrace> condition P A B >>= g \<lbrace>R\<rbrace>!"
proof -
  assume a1:"\<forall> s. Q s \<longrightarrow> P s"
  assume a2:"\<lbrace>\<lambda> s. Q s \<and> P s\<rbrace> A >>= g \<lbrace>R\<rbrace>!"
  then obtain B where y1:"\<lbrace>\<lambda>s. Q s \<and> P s\<rbrace> A \<lbrace>B\<rbrace>!" and y2:"\<forall>r. \<lbrace>B r\<rbrace> g r \<lbrace>R\<rbrace>!" using validNF_bind_split[OF a2] by auto
  thus ?thesis using validNF_bind[OF _ y1] by (metis (mono_tags) a1 condition_sufficient_left validNF_seq_ext)
qed

lemma validNF_simple_tuple_return:"\<lbrace> P \<rbrace> return (nid, Suc 0) \<lbrace>\<lambda> r s. P s \<and> r = (nid, Suc 0) \<rbrace>!"
  apply wp
  by auto
    
    
lemma [simp]:"do x \<leftarrow>  (do y \<leftarrow> f ; g y od) ; h x od = do x \<leftarrow> f ; y \<leftarrow> g x ; h y od"
  by (simp add: NonDetMonad.bind_assoc)
  
        
lemma FillWindow_to_funspec:
"len_ws \<le> USHORT_MAX
\<Longrightarrow> Some win = waypoints_window_aux ws i len_ws_win
\<Longrightarrow> len_ws_win \<le> len_ws 
\<Longrightarrow> 0<len_ws_win
\<Longrightarrow> (\<forall> (s::lifted_globals) v a. a < len_ws_win  \<longrightarrow> lift_waypoints (heap_Waypoint_struct_C_update (\<lambda>b c. if c =  wsp +\<^sub>p len_ws +\<^sub>p int a then v b else b c) s) wsp len_ws = lift_waypoints s wsp len_ws)
\<Longrightarrow> \<lbrace>\<lambda> (s::lifted_globals).
  are_valid_Waypoints s ( wsp +\<^sub>p len_ws) len_ws_win
  \<and> are_valid_Waypoints s wsp len_ws
  \<and> ws = lift_waypoints s wsp len_ws \<rbrace>
  LoadCode.WaypointManagerUtils.FillWindow' wsp len_ws i len_ws_win ( wsp +\<^sub>p len_ws)
\<lbrace> \<lambda> r s. 
  are_valid_Waypoints s ( wsp +\<^sub>p len_ws) len_ws_win
  \<and> are_valid_Waypoints s wsp len_ws
  \<and> ws = lift_waypoints s wsp len_ws
  \<and> (\<forall> j. j <  len_ws_win \<longrightarrow> heap_Waypoint_struct_C s ( wsp +\<^sub>p len_ws +\<^sub>p j) = win ! j) 
  \<and> r = 1\<rbrace>!"
  apply (unfold LoadCode.WaypointManagerUtils.FillWindow'_def)
    apply wp
      apply(subst whileLoop_add_inv
        [where 
          M = "\<lambda> ((j,nid,success),s). len_ws_win - j"
          and I = 
            "\<lambda> (j,nid,success) s.
  are_valid_Waypoints s  (wsp +\<^sub>p len_ws) len_ws_win
  \<and>  are_valid_Waypoints s wsp len_ws
  \<and> ws = lift_waypoints s wsp len_ws
  \<and> j \<le> len_ws_win
\<and> (j = 0 \<longrightarrow> nid = sint i)
\<and> (0 < j \<longrightarrow> nid = sint (nextwaypoint_C (win ! (j - 1))))
\<and> (\<forall> k \<le> j - 1. 0 < j \<longrightarrow> heap_Waypoint_struct_C s ( wsp +\<^sub>p len_ws +\<^sub>p k) = win ! k)
\<and> success = 1
" ])
  apply (wp_once)
  apply(simp add: lift_lift_waypoint_agnostic_prop)
    apply clarsimp
    apply (rule findwp_success)
     apply rule
    apply(rule validNF_condition_tru)
      apply simp+
     apply wp
       apply clarsimp
    apply wp
       apply clarsimp
    apply wp
       apply clarsimp
    
         apply rule
  apply (metis (no_types, hide_lams) One_nat_def not_gr0 of_int_sint option.inject waypoint_window_aux_nextwp)
         apply rule+
  apply (meson MCWaypointSubSequence_to_funspec_supp4)    
          apply (metis diff_diff_cancel diff_zero less_nat_zero_code nat_le_Suc_less_imp not_gr0 zero_less_diff)
    apply linarith
        apply rule+
    using loadcode19 apply force
           apply rule+
         apply auto[1]
                 apply rule+
        apply blast
       apply rule+
    apply force
      apply rule+
       apply blast
      apply rule+
       apply blast
      apply clarsimp
          apply (meson MCWaypointSubSequence_to_funspec_supp1)
       by(auto split:option.splits)           
        
lemma GroomWindow_to_funspec_supp1:
  assumes a2:"Some win' = waypoints_window_aux ws i len_ws_win"
and a3:"wsp +\<^sub>p int len_ws +\<^sub>p int j = wsp +\<^sub>p int len_ws +\<^sub>p (int len_ws_win - 1)"
and a4:"j < len_ws_win"
and a5:"len_ws_win \<le> USHORT_MAX"
and a6:"(\<forall> j. j <  len_ws_win \<longrightarrow> heap_Waypoint_struct_C s (wsp +\<^sub>p len_ws +\<^sub>p j) = win' ! j)"
and a7:"Some win = waypoints_window ws i len_ws_win"
shows "nextwaypoint_C_update (\<lambda>a. number_C (heap_Waypoint_struct_C s (wsp +\<^sub>p int len_ws +\<^sub>p (int len_ws_win - 1))))
                (heap_Waypoint_struct_C s (wsp +\<^sub>p int len_ws +\<^sub>p (int len_ws_win - 1))) =
               win ! j"
proof -
  have y1:"len_ws_win - 1 \<le> USHORT_MAX" using a5 by auto
  have y2:"j \<le> USHORT_MAX" using a4 y1 by auto 
  have y3:"j = len_ws_win - 1" using a3 ptr_offset_equality[OF y2 y1, where p="wsp +\<^sub>p int len_ws"] a4 by auto
  have y4:" last win' = win' ! j" by (metis a2 a4 gr_implies_not0 last_conv_nth length_0_conv waypoints_window_aux_success_length y3)
  have y5:"win = (butlast win') @ [nextwp_update (last win') (number_C (last win'))]" using a7 a2 waypoints_window_aux_to_waypoints_window_success_rel nextwp_update_def by auto
  have y6:"win = (butlast win) @ [nextwp_update (win' ! j) (number_C (win' ! j))]" using y4 y5 by auto
  have y7:"length win = len_ws_win"
    by (metis (mono_tags, lifting) One_nat_def Suc_eq_plus1 Suc_pred' a2 a4 add.commute append_eq_append_conv dual_order.strict_trans1 eq_imp_le eq_refl gr_zeroI length_Cons length_append length_butlast length_neq list.size(3) not_less0 not_less_zero size_ne_size_imp_ne snoc_eq_iff_butlast waypoints_window_aux_success_length y3 y4 y4 y5 y6)
  have y8:"win ! j = nextwp_update (win' ! j) (number_C (win' ! j))" using  y6 y7 y3 by (metis length_butlast nth_append_length)
  thus ?thesis using y8 nextwp_update_def y3 a6 a4 by auto 
qed
      
lemma GroomWindow_to_funspec_supp2:
assumes a3:"Some win' = waypoints_window_aux (lift_waypoints s wsp len_ws) i len_ws_win"
and a5:"Some win = waypoints_window ws i len_ws_win"
and a8: "ws = lift_waypoints s wsp len_ws"
and a10:"wsp +\<^sub>p int len_ws +\<^sub>p int j \<noteq> wsp +\<^sub>p int len_ws +\<^sub>p (int len_ws_win - 1)" 
and a11:"j < len_ws_win"
shows "win' ! j = win ! j"
proof -
  have y3:"j < len_ws_win - 1"  using a10 a11 nat_less_cases' by fastforce
  thus ?thesis
    by (metis (no_types, lifting) a11 a3 a5 a8 append_butlast_last_id length_butlast length_ineq_not_Nil(1) nth_append waypoints_window_aux_success_length waypoints_window_aux_to_waypoints_window_success_rel)
qed
      
lemma GroomWindow_to_funspec:
"(\<forall> (s::lifted_globals) v a. a < len_ws_win  \<longrightarrow> lift_waypoints (heap_Waypoint_struct_C_update (\<lambda>b c. if c =  wsp +\<^sub>p int len_ws +\<^sub>p int a then v b else b c) s) wsp len_ws = lift_waypoints s wsp len_ws)
\<Longrightarrow> len_ws \<le> USHORT_MAX
\<Longrightarrow> len_ws_win \<le> len_ws 
\<Longrightarrow> 0<len_ws_win
\<Longrightarrow> Some win' = waypoints_window_aux ws i len_ws_win \<Longrightarrow>
\<lbrace>\<lambda> (s::lifted_globals).
  are_valid_Waypoints s (wsp +\<^sub>p len_ws) len_ws_win
  \<and> are_valid_Waypoints s wsp len_ws
  \<and> ws = lift_waypoints s wsp len_ws
 \<and> (\<forall> j. j <  len_ws_win \<longrightarrow> heap_Waypoint_struct_C s (wsp +\<^sub>p len_ws +\<^sub>p j) = win' ! j)
 \<and> P s
\<rbrace>
  LoadCode.WaypointManagerUtils.GroomWindow' len_ws_win (wsp +\<^sub>p len_ws)
\<lbrace> \<lambda> r s. 
  are_valid_Waypoints s (wsp +\<^sub>p len_ws) len_ws_win
  \<and> are_valid_Waypoints s wsp len_ws
  \<and> ws = lift_waypoints s wsp len_ws
  \<and> (\<forall> j. j <  len_ws_win \<longrightarrow> heap_Waypoint_struct_C s (wsp +\<^sub>p len_ws +\<^sub>p j) = (butlast win' @ [nextwp_update (last win') (number_C (last win'))]) ! j) \<rbrace>!"
  apply (subgoal_tac "len_ws_win - 1 < len_ws_win")
  apply (subgoal_tac "\<exists> win. Some win = waypoints_window ws i len_ws_win")
  apply (subgoal_tac "\<And> (s::lifted_globals) v.  lift_waypoints s wsp len_ws = lift_waypoints (heap_Waypoint_struct_C_update (\<lambda>b c. if c =  wsp +\<^sub>p int len_ws +\<^sub>p (int len_ws_win - 1) then v b else b c) s) wsp len_ws")
  apply (unfold LoadCode.WaypointManagerUtils.GroomWindow'_def)
  apply wp
     apply (clarsimp | rule conjI impI)+
     using lift_lift_waypoint_agnostic_prop[of "len_ws_win - 1"] apply (auto split: option.splits simp add: GroomWindow_to_funspec_supp1 GroomWindow_to_funspec_supp2)
    by (metis (hide_lams) are_valid_Waypoints_def One_nat_def Suc_le_eq le_less neq0_conv of_nat_1 of_nat_diff zero_less_diff)+

      
lemma FillWindow_ignore_output:"\<lbrace> P \<rbrace> do WaypointManagerUtils.FillWindow' wsp len_ws i len_ws_win (wsp +\<^sub>p int len_ws); g od \<lbrace> Q \<rbrace>! \<Longrightarrow> \<lbrace> P \<rbrace>  do ret' \<leftarrow> WaypointManagerUtils.FillWindow' wsp len_ws i len_ws_win (wsp +\<^sub>p int len_ws); g od \<lbrace> Q \<rbrace>!"
  by auto
    
        
lemma FillAndGroomWaypoint_to_funspec:
"len_ws \<le> USHORT_MAX
\<Longrightarrow> waypoints_wf ws
\<Longrightarrow> Some win' = waypoints_window_aux ws i len_ws_win
\<Longrightarrow> len_ws_win \<le> len_ws 
\<Longrightarrow> 0<len_ws_win
\<Longrightarrow> (\<forall> (s::lifted_globals) v a. a < len_ws_win  \<longrightarrow> lift_waypoints (heap_Waypoint_struct_C_update (\<lambda>b c. if c = wsp +\<^sub>p len_ws +\<^sub>p int a then v b else b c) s) wsp len_ws = lift_waypoints s wsp len_ws)
\<Longrightarrow> \<lbrace>\<lambda> (s::lifted_globals).
  are_valid_Waypoints s (wsp +\<^sub>p len_ws) len_ws_win
  \<and> are_valid_Waypoints s wsp len_ws
  \<and> ws = lift_waypoints s wsp len_ws \<rbrace>
  LoadCode.WaypointManagerUtils.AutoPilotMissionCommandSegment' wsp len_ws i (wsp +\<^sub>p len_ws) len_ws_win 
\<lbrace> \<lambda> r s. 
  are_valid_Waypoints s (wsp +\<^sub>p len_ws) len_ws_win
  \<and> are_valid_Waypoints s wsp len_ws
  \<and> ws = lift_waypoints s wsp len_ws
  \<and> (\<exists> win. Some win = waypoints_window ws i len_ws_win
    \<and> (\<forall> j. j <  len_ws_win \<longrightarrow> heap_Waypoint_struct_C s (wsp +\<^sub>p len_ws +\<^sub>p j) = win ! j)) \<rbrace>!"
  apply (unfold LoadCode.WaypointManagerUtils.AutoPilotMissionCommandSegment'_def)
  apply wp_once
   defer
   apply(rule FillWindow_to_funspec)
       apply(assumption)+
  apply wp_once_trace
   apply clarsimp
    apply (rule validNF_return)
  apply wp_once
   apply(simp split:option.splits)
   apply rule
    apply rule
    apply simp
   apply rule
   apply rule
    apply clarsimp
   apply(rule GroomWindow_to_funspec[where i=i])
    apply(assumption )+
    apply simp
  apply clarsimp
  apply simp
done

end