theory MissionCommandUtils imports 
"/home/dacosta/dev/rc/l4v/tools/autocorres/AutoCorres"
begin

install_C_file "MissionCommandUtils.c"
autocorres[ts_rules = nondet, heap_abs_syntax] "MissionCommandUtils.c"  
  
(* A mission type is a tuple where the first component is a list of waypoints and the second 
   component is the starting waypoint for the mission. *)
type_synonym mission = "Waypoint_struct_C list \<times> 64 signed word"

definition get_waypoint_ptr_ptr where
  "get_waypoint_ptr_ptr s mcp n \<equiv> (waypointlist_C (heap_MissionCommand_struct_C s mcp)) +\<^sub>p n"

definition get_waypoint_ptr where
  "get_waypoint_ptr s mcp n \<equiv> heap_Waypoint_struct_C'ptr s (get_waypoint_ptr_ptr s mcp n)"
  
definition get_waypoint where
  "get_waypoint s mcp n \<equiv> heap_Waypoint_struct_C s (get_waypoint_ptr s mcp n)"

definition get_waypoints_length where
  "get_waypoints_length s mcp \<equiv> length_C (waypointlist_ai_C (heap_MissionCommand_struct_C s mcp))"

definition is_valid_MissionCommand where 
  "is_valid_MissionCommand s mcp \<equiv> 
    is_valid_MissionCommand_struct_C s mcp
    \<and> (\<forall> j < unat (get_waypoints_length s mcp).
        is_valid_Waypoint_struct_C'ptr s (get_waypoint_ptr_ptr s mcp j)
        \<and> is_valid_Waypoint_struct_C s (get_waypoint_ptr s mcp j))"

lemma get_waypoint_ptr_valid: 
  "is_valid_MissionCommand s mcp
  \<Longrightarrow> n < unat (get_waypoints_length s mcp)
  \<Longrightarrow> \<forall> k< n. is_valid_Waypoint_struct_C s (get_waypoint_ptr s mcp k)"  
  apply(induct n)
  using Suc_lessD is_valid_MissionCommand_def less_antisym by blast+
  
fun lift_waypoints  where
  "lift_waypoints s mcp 0 = []"
| "lift_waypoints s mcp (Suc n) = lift_waypoints s mcp n @ [get_waypoint s mcp n]" 

lemma lift_waypoints_butlast:
  "ws = lift_waypoints s mcp n \<Longrightarrow> n = 0 \<or> butlast ws = lift_waypoints s mcp (n - 1)"
 apply(induct n arbitrary: ws) by auto

lemma empty_lift_waypoints_zero[simp]:  "[] = lift_waypoints s p n \<Longrightarrow> n = 0"
apply(induct n) by auto
  
lemma nonempty_lift_waypoints_nonzero[simp]: "Cons w ws = lift_waypoints s p n \<Longrightarrow> n > 0" 
  using not_gr_zero by fastforce

lemma lift_waypoints_length: "ws = lift_waypoints s mcp n \<Longrightarrow> length ws = n"
  apply(induct n arbitrary: ws) by auto  
 
lemma lift_waypoints_to_get_waypoint: 
  "ws = lift_waypoints s mcp n \<Longrightarrow> \<forall> k< n.  get_waypoint s mcp k = nth ws k"
apply(induct n arbitrary: ws) by (auto simp add: less_Suc_eq lift_waypoints_length nth_append)

lemma lift_waypoints_append:
"(lift_waypoints s mcp n) @ [(get_waypoint s mcp n)] = lift_waypoints s mcp (Suc n)"
  apply(induct n)
    apply(auto)
  done
    
fun find_waypoint :: "Waypoint_struct_C list \<Rightarrow> 64 signed word \<Rightarrow> Waypoint_struct_C option" where
  "find_waypoint [] i = None"
| "find_waypoint (w#ws) i = (if (number_C w = i) then Some w else find_waypoint ws i)"
    
lemma ptr_adds_collapse[simp]: "x +\<^sub>p y +\<^sub>p z = x +\<^sub>p (y + z)" 
  by (metis (no_types, hide_lams) 
      ab_semigroup_add_class.add_ac(1) 
      distrib_left 
      mult.commute 
      of_int_add 
      ptr.exhaust 
      ptr_add_def')
    
lemma find_waypoint_finds_first: 
"Some w = find_waypoint ws i    
\<Longrightarrow> (\<exists> ws1 ws2. ws1 @ [w] @ ws2 = ws \<and> None = find_waypoint ws1 i \<and> w = ws ! length ws1)"
proof(induct "length ws" arbitrary: ws)
  case 0
  then show ?case by auto
next
  case (Suc n)    
  then have "w = hd ws \<or> (Some w = find_waypoint (tl ws) i \<and> w \<noteq> hd ws)" 
    by (metis find_waypoint.simps(2) hd_conv_nth length_SucE list.sel(3) list.size(3) nat.simps(3) nth_Cons_0 option.inject)
  thus ?case
  proof
    assume "w = hd ws"
    thus ?case by (metis Suc append_Cons append_Nil find_waypoint.simps hd_Cons_tl length_greater_0_conv list.size nth_Cons_0 zero_less_Suc)
  next
    assume a:"Some w = find_waypoint (tl ws) i \<and> w \<noteq> hd ws"    
    then have y1:"n = length (tl ws)" using Suc by auto
    then obtain ws1 ws2 where y2:"ws1 @ [w] @ ws2 = tl ws" and y3:"None = find_waypoint ws1 i" and y4:"w = tl ws ! length ws1" using  y1 a Suc by blast    
    then have y5:"hd ws # ws1 @ [w] @ ws2 = ws" using Suc by (metis list.collapse list.size(3) nat.simps(3))
    then have y6:"w \<noteq> hd ws" using a by blast
    then have y7:"None = find_waypoint (hd ws # ws1) i" using a y3 Suc.prems option.inject y5 by fastforce
    then have y8:"w = ws ! length (hd ws # ws1)" by (metis length_Cons nth_Cons_Suc y2 y5 y4)
    thus ?case using y5 y7 by (metis append_Cons)
  qed
qed

lemma find_waypoint_none_extend: 
"None = find_waypoint ws i
\<Longrightarrow> number_C w \<noteq> i 
\<Longrightarrow> None = find_waypoint (ws @[w]) i"
proof(induct ws)
  case Nil
  thus ?case by auto
next 
  case (Cons w ws)
  thus ?case by (simp add: Cons.prems(1))
qed 
  
  
lemma [simp]: "length_C s[mcp]\<rightarrow>waypointlist_ai = get_waypoints_length s mcp"
  by (simp add: MissionCommandUtils.get_MissionCommand_struct_waypointlist_ai_def get_waypoints_length_def)

lemma [simp]: "s[mcp]\<rightarrow>waypointlist +\<^sub>p uint n = get_waypoint_ptr_ptr s mcp (uint n)" 
  by (simp add: MissionCommandUtils.get_MissionCommand_struct_waypointlist_def get_waypoint_ptr_ptr_def)
    
lemma [simp]: "s[get_waypoint_ptr_ptr s mcp (uint n)] = get_waypoint_ptr s mcp (uint n)"
  by (simp add: get_waypoint_ptr_def)

lemma [simp]: "s[get_waypoint_ptr s mcp (uint n)] = get_waypoint s mcp (uint n)"
  by (simp add: get_waypoint_def)
    
lemma [simp]: " s[get_waypoint_ptr s mcp (uint j)]\<rightarrow>number = number_C (get_waypoint s mcp (uint j))"
  using MissionCommandUtils.get_Waypoint_struct_number_def by auto      
  
lemma findwp_success_aux1[simp]: "(a::32 word) < n \<Longrightarrow> unat (n - (a + 1)) < unat (n - a)"
proof -
  assume "a < n"
  then have "0 \<noteq> n - a"
    by force
  then show ?thesis
    by (simp add: add.commute diff_add_eq_diff_diff_swap measure_unat)
qed

lemma c:"get_waypoint s mcp (uint i) = ws ! (unat i) 
\<Longrightarrow> w = ws ! length ws1
\<Longrightarrow> ws1 @ [w] @ ws2 = ws 
\<Longrightarrow> None = find_waypoint ws1 (number_C (get_waypoint s mcp (uint i))) 
\<Longrightarrow> length ws1 = unat i"
  sorry
    
lemma findwp_success_aux3:
  assumes a1:"Some w = find_waypoint (lift_waypoints s mcp (unat (get_waypoints_length s mcp))) (number_C (get_waypoint s mcp (uint j)))"
  and  a2:"None = find_waypoint (lift_waypoints s mcp (unat j)) (number_C (get_waypoint s mcp (uint j)))"
  and a3:"j < get_waypoints_length s mcp"
shows "get_waypoint s mcp (uint j) = w" 
proof -
  obtain ws where y1:"ws = lift_waypoints s mcp (unat (get_waypoints_length s mcp))" by auto
  obtain ws1 ws2 where y2:"ws1 @ [w] @ ws2 = ws"
            and y3:"None = find_waypoint ws1 (number_C (get_waypoint s mcp (uint j)))"
            and y4:" w = ws ! length ws1" using find_waypoint_finds_first a1 y1 by blast
  then have y5:"get_waypoint s mcp (uint j) = ws ! (unat j)" using a3 y1 by (simp add: lift_waypoints_to_get_waypoint uint_nat word_less_nat_alt)
  then have "unat j = length ws1" using c y5 y4 y2 y3 by fastforce
  thus ?thesis using y5 y4 by auto
qed  

  
lemma findwp_success_aux4:
  assumes a1:"None = find_waypoint (lift_waypoints s mcp (unat (j::32 word))) i"
and a2:"number_C (get_waypoint s mcp (uint j)) \<noteq> i"
and a3:"j < k"
shows "None = find_waypoint (lift_waypoints s mcp (unat (j + 1))) i"
proof -
  have y1:"None = find_waypoint ( lift_waypoints s mcp (unat j) @ [get_waypoint s mcp (uint j)]) i" using a1 a2 find_waypoint_none_extend by blast
  then have y2:"None = find_waypoint (lift_waypoints s mcp (Suc (unat j))) i" by (metis lift_waypoints_append uint_nat)
  then have y3:"(unat j) + 1 = unat (j + 1)" using a3 
    by (metis Suc_eq_plus1 add.commute less_is_non_zero_p1 unatSuc)
  thus ?thesis using Suc_eq_plus1 y2 by presburger
qed
    

  

lemma findwp_success:
"\<lbrace> \<lambda> (s::lifted_globals).
  is_valid_MissionCommand s mcp
  \<and> Some w = find_waypoint (lift_waypoints s mcp (unat (get_waypoints_length s mcp))) i
  \<and> P s\<rbrace>
  MissionCommandUtils.MissionCommandUtils.FindWP' mcp i
\<lbrace> \<lambda> r s. heap_Waypoint_struct_C s r = w \<and> P s\<rbrace>!"
(*  apply (rule validNF_assume_pre) *)
  apply (unfold MissionCommandUtils.MissionCommandUtils.FindWP'_def)
  apply (simp add: skipE_def)
  apply(subst whileLoopE_add_inv[where M = "\<lambda> (j,s). unat (get_waypoints_length s mcp - j)"
                                 and I = "\<lambda> j s. P s 
\<and> is_valid_MissionCommand s mcp
\<and> Some w = find_waypoint (lift_waypoints s mcp (unat (get_waypoints_length s mcp))) i
\<and> None = find_waypoint (lift_waypoints s mcp (unat j)) i
\<and> j \<le> get_waypoints_length s mcp
"])
  apply wp
    apply clarsimp
    apply auto
    using findwp_success_aux3 apply blast
             apply (simp add: is_valid_MissionCommand_def uint_nat word_less_nat_alt)
            apply (simp add: is_valid_MissionCommand_def uint_nat word_less_nat_alt)
    using is_valid_MissionCommand_def apply auto[1]
    using findwp_success_aux4 apply blast
    using inc_le apply blast
    using is_valid_MissionCommand_def apply blast
       apply (simp add: is_valid_MissionCommand_def uint_nat word_less_nat_alt)
       apply (simp add: is_valid_MissionCommand_def uint_nat word_less_nat_alt)
    using is_valid_MissionCommand_def apply blast
    apply (unfold is_valid_MissionCommand_def)
    apply wp
    apply auto
 done
end