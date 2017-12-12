theory LoadCode imports 
"AutoCorres"
begin
  
install_C_file "./WaypointManagerUtils.c"
  
autocorres[ts_rules = nondet, unsigned_word_abs = FillWindow FindWaypoint GroomWindow AutoPilotMissionCommandSegment ] "./WaypointManagerUtils.c"  
  
(* IMPORTANT:
 * The waypoint manager is going to at least store two array both with a maximum possible size of 
 * 2^16-1. If the size of the waypoint data structure times 2*16-1 is not less than or equal to 
 * the 2^32-1 Then we will no longer be able to gaurantee that a write to a mission command segment
 * will not alter the original mission command.
 * NB: I am assuming that maximum array size for LCMP messages is 2^16-1
 *)
lemma sanity_check_waypoint_size:"USHORT_MAX * size_of TYPE(Waypoint_struct_C) \<le> UINT_MAX"
  apply(unfold USHORT_MAX_def UINT_MAX_def) by simp

(* If the above lemma holds then this lemma will be true. Though I am not sure how to prove it. *)
lemma ptr_offset_equality:"a \<le> USHORT_MAX \<Longrightarrow> b \<le> USHORT_MAX  \<Longrightarrow> (p::Waypoint_struct_C ptr) +\<^sub>p a = p +\<^sub>p b \<Longrightarrow> a = b"
  sorry   

(* A subset of what we expect a valid mission command to entail. I.E, the ptr to the front
 * of the waypoint pointer array is valid, all elements in that array are valid and all pointers
 * to waypoints are valid. 
 *)     
definition are_valid_Waypoints where 
  "are_valid_Waypoints s wsp (len::nat) \<equiv> 
    is_valid_Waypoint_struct_C s wsp
    \<and> wsp \<noteq> NULL
    \<and> (\<forall> j < len. is_valid_Waypoint_struct_C s (wsp +\<^sub>p j)) "
  
lemma valid_waypoints[simp]:
"are_valid_Waypoints s wsp len 
\<Longrightarrow> j < len
\<Longrightarrow> is_valid_Waypoint_struct_C s (wsp +\<^sub>p j)"
  by (simp add: are_valid_Waypoints_def uint_nat word_less_nat_alt)
    
(* Generally useful lemma showing obvious things." *)  
lemma loadcode1[simp]: "(a::32 word) < n \<Longrightarrow> unat (n - (a + 1)) < unat (n - a)"
proof -
  assume "a < n"
  then have "0 \<noteq> n - a"
    by force
  then show ?thesis
    by (simp add: add.commute diff_add_eq_diff_diff_swap measure_unat)
qed
  
lemma loadcode2[simp]: "(a::16 word) < n \<Longrightarrow> unat (n - (a + 1)) < unat (n - a)"
proof -
  assume "a < n"
  then have "0 \<noteq> n - a"
    by force
  then show ?thesis
    by (simp add: add.commute diff_add_eq_diff_diff_swap measure_unat)
qed

lemma loadcode3[simp]: "uint (a::16 word) < uint n \<Longrightarrow> unat (n - (a + 1)) < unat (n - a)"
proof -
  assume "uint a < uint n"
  then have "0 \<noteq> n - a"
    by force
  then show ?thesis
    by (simp add: add.commute diff_add_eq_diff_diff_swap measure_unat)
qed
lemma loadcode4[simp]:"65535 \<le> x \<Longrightarrow> uint (a::16 word) \<le> x = True"
  using word.uint[of a] by auto
    
lemma loadcode5[simp]:"i < 0 \<Longrightarrow> i < uint (j::16 word)"
  by (metis less_trans neq_iff uint_lt_0)
    
lemma loadcode6[simp]:"INT_MIN < uint (len_ws_win::16 word)"
  using INT_MIN_def by fastforce
    
lemma loadcode7[simp]:"uint j < uint (x::16 word) - 1 \<Longrightarrow> j + 1 \<le> x"
  by (meson inc_le le_less word_less_def zle_diff1_eq)
 
lemma loadcode8[simp]:"int USHORT_MAX \<le> 2147483646"
proof -
  have "int USHORT_MAX = 65535" using USHORT_MAX_def by auto
  thus ?thesis by auto
qed    

lemma loadcode9[simp]:"uint (j::16 word) < uint (x::16 word) - 1 \<Longrightarrow> 0 < (j + 1)"
  by (metis (mono_tags, hide_lams) add.commute add_left_cancel le_less max_word_max not_less word_less_def word_neq_0_conv word_overflow zle_diff1_eq)

lemma loadcode10[simp]:"i \<le> 2147483645  \<Longrightarrow> int i < 2147483646"
  apply (induct i) by auto

lemma max_short_fix:"i \<le> USHORT_MAX \<Longrightarrow> int i < 2147483646"  
proof(induct i)
  case 0
  then show ?case by auto
next
  case (Suc i)
  then have "i < 2147483646" by auto
  then have "Suc i < 2147483646 \<or> Suc i = 2147483646" by auto
  thus ?case
  proof
    assume "Suc i < 2147483646"
    thus ?case by auto
  next
    assume "Suc i = 2147483646"
    thus ?case using Suc by (simp add: USHORT_MAX_def)
  qed
qed
    
lemma loadcode11[simp]:"c \<le> USHORT_MAX \<Longrightarrow> b \<le> c \<Longrightarrow> a < b \<Longrightarrow> int a \<le> 2147483646"
  by (meson le_less less_le_trans max_short_fix)

lemma loadcode12[simp]:"(of_nat USHORT_MAX::16 word) = 65535"
  apply (unfold of_nat_def USHORT_MAX_def)
   by (metis of_nat_def of_nat_numeral)

lemma loadcode13[simp]:"(65535::16 word) + 1 = 0"
  by simp

lemma loadcode14[simp]:"(i::16 word) + 1 = 0 \<Longrightarrow> i = 65535"
  by (metis add.commute add_left_cancel loadcode13) 

lemma loadcode15[simp]:"unat (0xffff::16 word) = USHORT_MAX"
  apply (unfold of_nat_def USHORT_MAX_def) 
  by simp
    
lemma loadcode16:"(i::16 word) + 1 = 0 \<Longrightarrow> unat i = USHORT_MAX"    
  using loadcode14 loadcode15 by blast  
    
lemma loadcode17:"(i < ((of_nat USHORT_MAX)::16 word)) = (i < i + 1)"
  apply auto
  using less_is_non_zero_p1 word_overflow apply blast
  by (metis le_less less_is_non_zero_p1 loadcode13 not_less)

lemma loadcode18[simp]:"i \<le> USHORT_MAX \<Longrightarrow> unat (of_nat i::16 word) = i"
  by (metis  le_unat_uoi loadcode15)

lemma loadcode19[simp]:"i \<le> USHORT_MAX \<Longrightarrow> uint ((of_nat i)::16 word) = int i"
  by (metis uint_nat loadcode18)
    
lemma loadcode20[simp]:"int len_ws_win \<le> 2147483648 \<Longrightarrow> 0 < len_ws_win \<Longrightarrow> int len_ws_win - 1 \<le> INT_MAX"
  by (simp add: INT_MAX_def)
    
lemma loadcode21[simp]:"0 < len_ws_win \<Longrightarrow> INT_MIN < int len_ws_win"
  by (simp add: INT_MIN_def)
    
lemma loadcode22[simp]:"len_ws \<le> USHORT_MAX \<Longrightarrow> len_ws_win \<le> len_ws \<Longrightarrow> int len_ws_win \<le> 2147483648"
  using max_short_fix by fastforce
       
lemma loadcode23:"0 < a \<Longrightarrow> a \<le> INT_MAX \<Longrightarrow> uint (of_nat a::32 word) - 1 < uint (of_nat a::32 word)"
  by simp
    
lemma loadcode24:"a < b \<Longrightarrow> b \<le> nat INT_MAX \<Longrightarrow> unat (of_nat a::32 word) < b"
proof(induct a arbitrary: b)
  case 0
  then show ?case by auto
next
  case (Suc a)
  then have y1:"a < (b - 1)" by auto
  then have y2:"b - 1 \<le> nat INT_MAX" using Suc by auto
  then have y3:"unat (of_nat a::32 word) < b - 1" using Suc y1 y2 by auto
  then have y4:"a < nat INT_MAX" using Suc by linarith
  thus ?case
    by (metis Divides.mod_less_eq_dividend Suc.prems(1) le_trans not_less unat_of_nat)
qed

lemma loadcode25:"0 < a \<Longrightarrow> a \<le> INT_MAX \<Longrightarrow> uint (of_nat a::32 word) \<le> INT_MAX"
proof(induct a)
  case 0
  then show ?case by auto
next
  case (Suc a)
  then obtain a' where y1:"a' = nat a" and y2:"a' \<le> nat INT_MAX" by force
  then have "a' = nat INT_MAX \<or> a' < nat INT_MAX" by auto
  thus ?case
  proof 
    assume "a' = nat INT_MAX"
    thus ?case using Suc.prems(2) y1 by linarith
  next
    assume "a' < nat INT_MAX"
    thus ?case 
      by (metis (mono_tags, hide_lams) Suc.prems(2) le_less not_le
          order_trans uint_nat word_of_nat_less zless_nat_eq_int_zless)
   qed
qed

lemma loadcode26[simp]:"0 < a \<Longrightarrow> a \<le> INT_MAX \<Longrightarrow> uint (of_nat a::32 word) - 1 \<le> INT_MAX"
  by (meson le_less loadcode23 loadcode25 order_trans)
        
   
end