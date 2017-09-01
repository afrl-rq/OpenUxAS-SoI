theory MissionCommandUtils imports 
"/home/dacosta/dev/rc/l4v/tools/autocorres/AutoCorres"
begin

install_C_file "MissionCommandUtils.c"
autocorres[ts_rules = nondet, heap_abs_syntax] "MissionCommandUtils.c"  

(* Various simplifying definitions to make working with waypoints through a mission command 
 * pointer less tedious.  
 *)
definition get_waypoint_ptr_ptr where
  "get_waypoint_ptr_ptr s mcp n \<equiv> (waypointlist_C (heap_MissionCommand_struct_C s mcp)) +\<^sub>p n"

definition get_waypoint_ptr where
  "get_waypoint_ptr s mcp n \<equiv> heap_Waypoint_struct_C'ptr s (get_waypoint_ptr_ptr s mcp n)"
  
definition get_waypoint where
  "get_waypoint s mcp n \<equiv> heap_Waypoint_struct_C s (get_waypoint_ptr s mcp n)"

definition get_waypoints_length where
  "get_waypoints_length s mcp \<equiv> length_C (waypointlist_ai_C (heap_MissionCommand_struct_C s mcp))"

(* The abreviations used by Autocorress are confusing and give the type inferencing engine a lot 
 * of trouble so lets rewrite the ones we will be working with.  
 *)
  
lemma [simp]: "length_C s[mcp]\<rightarrow>waypointlist_ai = get_waypoints_length s mcp"
  by (simp add: 
      MissionCommandUtils.get_MissionCommand_struct_waypointlist_ai_def 
      get_waypoints_length_def)

lemma [simp]: "s[mcp]\<rightarrow>waypointlist +\<^sub>p uint n = get_waypoint_ptr_ptr s mcp (uint n)" 
  by (simp add: MissionCommandUtils.get_MissionCommand_struct_waypointlist_def get_waypoint_ptr_ptr_def)
    
lemma [simp]: "s[get_waypoint_ptr_ptr s mcp (uint n)] = get_waypoint_ptr s mcp (uint n)"
  by (simp add: get_waypoint_ptr_def)

lemma [simp]: "s[get_waypoint_ptr s mcp (uint n)] = get_waypoint s mcp (uint n)"
  by (simp add: get_waypoint_def)
    
lemma [simp]: " s[get_waypoint_ptr s mcp (uint j)]\<rightarrow>number = number_C (get_waypoint s mcp (uint j))"
  using MissionCommandUtils.get_Waypoint_struct_number_def by auto      

(* A subset of what we expect a valid mission command to entail. I.E, the ptr to the front
 * of the waypoint pointer array is valid, all elements in that array are valid and all pointers
 * to waypoints are valid. 
 *)     
definition is_valid_MissionCommand where 
  "is_valid_MissionCommand s mcp \<equiv> 
    is_valid_MissionCommand_struct_C s mcp
    \<and> (\<forall> j < unat (get_waypoints_length s mcp).
        is_valid_Waypoint_struct_C'ptr s (get_waypoint_ptr_ptr s mcp j)
        \<and> is_valid_Waypoint_struct_C s (get_waypoint_ptr s mcp j))"

(* Lift waypoints from a mission command into a list with the same order. *)
fun lift_waypoints  where
  "lift_waypoints s mcp 0 = []"
| "lift_waypoints s mcp (Suc n) = lift_waypoints s mcp n @ [get_waypoint s mcp n]" 

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
  
lemma find_waypoint_none_extend_some: 
"None = find_waypoint ws i
\<Longrightarrow> number_C w = i 
\<Longrightarrow> Some w = find_waypoint (ws @[w]) i"
apply(induct ws) by auto
    
lemma word32_lt_nat_lt[simp]: "(a::32 word) < n \<Longrightarrow> unat (n - (a + 1)) < unat (n - a)"
proof -
  assume "a < n"
  then have "0 \<noteq> n - a"
    by force
  then show ?thesis
    by (simp add: add.commute diff_add_eq_diff_diff_swap measure_unat)
qed

    
lemma prefix_ident: "prefix ws' ws \<Longrightarrow> \<exists> ws1. ws = ws'@ws1"
  apply (induct ws' arbitrary: ws) 
  using prefix_def by blast+
  
lemma find_waypoint_prefix_ext:
  "prefix ws' ws \<Longrightarrow> Some w = find_waypoint ws' n \<Longrightarrow> Some w = find_waypoint ws n"
proof(induct ws' arbitrary: ws)
  case Nil
  then show ?case by auto
next
  case (Cons w' ws'')
  then have "number_C w' = n \<or> number_C w' \<noteq> n" by auto
  thus ?case
  proof
    assume a:"number_C w' = n"
    then obtain ws1 where y1:"ws = w' # ws'' @ ws1" using prefix_ident Cons by (metis append_Cons)
    then have y2:"w' = w" using Cons a by auto
    then have "Some w' = find_waypoint (w' # ws'' @ ws1) n" using Cons a by auto
    thus ?case using y1 y2 by blast
  next
    assume a:"number_C w' \<noteq> n"
    then obtain ws1 where y1:"ws = w' # ws'' @ ws1" using prefix_ident Cons by (metis append_Cons)
    then have y2:"prefix ws'' (ws'' @ ws1)" using Cons by auto
    then have "Some w = find_waypoint ws'' n"  by (simp add: a Cons)
    thus ?case using Cons.hyps a find_waypoint.simps(2) y1 y2 by presburger
  qed
qed
  
lemma lifted_waypoint_prefixes:" i \<le> j \<Longrightarrow> prefix (lift_waypoints s mcp i) (lift_waypoints s mcp j)" 
proof(induct i)
  case 0
  then show ?case by auto
next
  case (Suc i)
  then show ?case by (metis lift_waypoints.simps(2) prefix_def prefix_order.lift_Suc_mono_le)
qed
  
lemma findwp_success_aux:
assumes a1:"Some w = find_waypoint (lift_waypoints s mcp (unat (get_waypoints_length s mcp))) (number_C (get_waypoint s mcp (uint j)))"
and  a2:"None = find_waypoint (lift_waypoints s mcp (unat j)) (number_C (get_waypoint s mcp (uint j)))"
and a3:"j < get_waypoints_length s mcp"
shows "get_waypoint s mcp (uint j) = w" 
proof -  
  have y1:"prefix (lift_waypoints s mcp (unat j) @ [get_waypoint s mcp (uint j)]) (lift_waypoints s mcp (unat (get_waypoints_length s mcp)))" 
    using lifted_waypoint_prefixes a3
    by (metis le_less less_antisym lift_waypoints_append not_less uint_nat word_less_nat_alt)
  then have y2:"Some (get_waypoint s mcp (uint j)) =  find_waypoint (lift_waypoints s mcp (unat j) @ [get_waypoint s mcp (uint j)]) (number_C (get_waypoint s mcp (uint j)))"
    using a2 find_waypoint_none_extend_some by blast
  show ?thesis using find_waypoint_prefix_ext y1 y2 a1 by (metis option.inject)
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
    using findwp_success_aux apply blast
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
      
lemma findwp_failure:
"\<lbrace> \<lambda> (s::lifted_globals).
  is_valid_MissionCommand s mcp
  \<and> None = find_waypoint (lift_waypoints s mcp (unat (get_waypoints_length s mcp))) i
  \<and> P s\<rbrace>
  MissionCommandUtils.MissionCommandUtils.FindWP' mcp i
\<lbrace> \<lambda> r s. r = NULL \<and> P s\<rbrace>!"
  apply (unfold MissionCommandUtils.MissionCommandUtils.FindWP'_def)
  apply (simp add: skipE_def)
  apply(subst whileLoopE_add_inv[where M = "\<lambda> (j,s). unat (get_waypoints_length s mcp - j)"
                                 and I = "\<lambda> j s. P s 
\<and> is_valid_MissionCommand s mcp
\<and> None = find_waypoint (lift_waypoints s mcp (unat (get_waypoints_length s mcp))) i
\<and> None = find_waypoint (lift_waypoints s mcp (unat j)) i
\<and> j \<le> get_waypoints_length s mcp
"])
    apply wp
    apply clarsimp
    apply auto
    sorry

end