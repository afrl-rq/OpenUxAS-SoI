theory LoadCode imports 
"/home/dacosta/dev/rc/l4v/tools/autocorres/AutoCorres"
begin
  
install_C_file "../CMASI/MissionCommandUtils.c"
  
autocorres[ts_rules = nondet, unsigned_word_abs = FillWindow FindWP GroomWindow FillAndGroomWindow ] "../CMASI/MissionCommandUtils.c"  
  

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
    
(* Generally useful lemma." *)  
lemma [simp]: "(a::32 word) < n \<Longrightarrow> unat (n - (a + 1)) < unat (n - a)"
proof -
  assume "a < n"
  then have "0 \<noteq> n - a"
    by force
  then show ?thesis
    by (simp add: add.commute diff_add_eq_diff_diff_swap measure_unat)
qed
  
lemma [simp]: "(a::16 word) < n \<Longrightarrow> unat (n - (a + 1)) < unat (n - a)"
proof -
  assume "a < n"
  then have "0 \<noteq> n - a"
    by force
  then show ?thesis
    by (simp add: add.commute diff_add_eq_diff_diff_swap measure_unat)
qed

lemma [simp]: "uint (a::16 word) < uint n \<Longrightarrow> unat (n - (a + 1)) < unat (n - a)"
proof -
  assume "uint a < uint n"
  then have "0 \<noteq> n - a"
    by force
  then show ?thesis
    by (simp add: add.commute diff_add_eq_diff_diff_swap measure_unat)
qed
  
lemma [simp]: "j < i \<Longrightarrow> int (unat j) = uint j" by (simp add: uint_nat)
    
lemma word16_leq_max_word16_as_int[simp]:"65535 \<le> x \<Longrightarrow> uint (a::16 word) \<le> x = True"
  using word.uint[of a] by auto
    
lemma [simp]:"i < 0 \<Longrightarrow> i < uint (j::16 word)"
  by (metis less_trans neq_iff uint_lt_0)
    
lemma [simp]:"INT_MIN < uint (len_ws_win::16 word)"
  using INT_MIN_def by fastforce
    
lemma [simp]:"uint j < uint (x::16 word) - 1 \<Longrightarrow> j + 1 \<le> x"
  by (meson inc_le le_less word_less_def zle_diff1_eq)
    

lemma [simp]:"int USHORT_MAX \<le> 2147483646"
proof -
  have "int USHORT_MAX = 65535" using USHORT_MAX_def by auto
  thus ?thesis by auto
qed    

lemma [simp]:"uint (j::16 word) < uint (x::16 word) - 1 \<Longrightarrow> 0 < (j + 1)"
  by (metis (mono_tags, hide_lams) add.commute add_left_cancel le_less max_word_max not_less word_less_def word_neq_0_conv word_overflow zle_diff1_eq)

lemma [simp]:"i \<le> 2147483645  \<Longrightarrow> int i < 2147483646"
  apply (induct i) by auto
  
lemma max_short_fix:"i \<le> USHORT_MAX \<Longrightarrow> int i < 2147483646"  
sorry
   
lemma [simp]:"i \<le> USHORT_MAX \<Longrightarrow> uint ((of_nat i)::16 word) = int i"
  sorry
    
lemma [simp]:"int len_ws_win \<le> 2147483648 \<Longrightarrow> 0 < len_ws_win \<Longrightarrow> int len_ws_win - 1 \<le> INT_MAX"
  sorry

lemma rename1[simp]:"int len_ws_win \<le> 2147483648 \<Longrightarrow> 0 < len_ws_win \<Longrightarrow> uint (of_nat len_ws_win) - 1 \<le> INT_MAX"
  sorry
    
lemma rename2[simp]:"0 < len_ws_win \<Longrightarrow> a \<le> USHORT_MAX \<Longrightarrow> uint (of_nat len_ws_win) - 1 \<le> INT_MAX"
  sorry
    
lemma rename3[simp]:"len_ws \<le> USHORT_MAX \<Longrightarrow> len_ws_win \<le> len_ws \<Longrightarrow> int len_ws_win \<le> 2147483648"
   using max_short_fix by fastforce
    
lemma [simp]:"0 < len_ws_win \<Longrightarrow> INT_MIN < int len_ws_win"
  sorry
    
lemma [simp]:"p +\<^sub>p int 0 = p"    
  sorry

lemma rename4[simp]:"(i::nat) < j \<Longrightarrow> \<not> int i < int j - 1 \<Longrightarrow> i = j - 1"
  by linarith
    
lemma rename5[simp]:"a \<le> USHORT_MAX \<Longrightarrow> int a < 2147483648"
  sorry

lemma rename6[simp]:"a \<le> USHORT_MAX \<Longrightarrow> b \<le> a \<Longrightarrow> int b \<le> 2147483647"
  sorry
    
lemma USHORT_MAX_LT_UINT_MAX[simp]:"x \<le> USHORT_MAX \<Longrightarrow> x \<le> UINT_MAX"
  sorry
    
lemma noninter_pointer_add[simp]:"j \<le> USHORT_MAX \<Longrightarrow> 0 < j \<Longrightarrow> i < j \<Longrightarrow> ap +\<^sub>p i = ap +\<^sub>p j \<Longrightarrow> False"
  sorry

lemma rename7[simp,wp]:"a \<le> USHORT_MAX \<Longrightarrow> b < a  \<Longrightarrow> b \<le> 2147483648" 
  sorry

lemma rename8[simp,wp]:"a \<le> USHORT_MAX \<Longrightarrow> b < a - 1  \<Longrightarrow> int b \<le> 2147483646" 
  sorry
    
end