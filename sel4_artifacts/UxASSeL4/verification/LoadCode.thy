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
lemma sanity_check_waypoint_size:"USHORT_MAX * size_of TYPE(Waypoint_struct_C) < UINT_MAX"
  apply(unfold USHORT_MAX_def UINT_MAX_def) by simp

lemma uxas_array_length_lt_uint_max:"a \<le> USHORT_MAX \<Longrightarrow> a * size_of TYPE(Waypoint_struct_C) < UINT_MAX"
  using sanity_check_waypoint_size by auto

lemma word32_addition_ineq1:"(p1::32 word) \<noteq> p2 \<Longrightarrow> x < UINT_MAX \<Longrightarrow> (p1::32 word) + of_nat x \<noteq> p2 + of_nat x"
 by simp    
    
lemma word32_identity1:"(p::32 word) = 0xffffffff \<or> p < 0xffffffff"
  proof(induct p)
    case 1
    then show ?case by auto
  next
    case (2 p)
    then have "p = 0xFFFFFFFF \<or> p < 0xFFFFFFFF" by auto
    thus ?case
    proof
      assume "p = 0xFFFFFFFF"
      then have "1 + p = 0" by auto
      thus ?case using 2 by auto
    next
      assume "p < 0xFFFFFFFF"
      then have "p + 1 \<le> 0xFFFFFFFF" using inc_le by blast
      then have "1 + p \<le> 0xFFFFFFFF" by (simp add: add.commute)
      thus ?case by auto
    qed
  qed

    
    
lemma word32_identity2:"(p::32 word) = 0xffffffff \<Longrightarrow> p + 1 = 0" by simp

lemma max_word32_to_nat:"unat (0xFFFFFFFF::32 word) = 4294967295"
  by auto
    
lemma of_nat_eq_overflow_or_not:"(of_nat y::32 word)  = x \<Longrightarrow> (4294967295 < y \<or> y = unat x)"
 proof(induct y arbitrary: x)
   case 0
   then show ?case by auto
 next
   case (Suc y)
   then have "4294967295 < y \<or> y = unat (x - 1)"  by fastforce
   thus ?case
   proof
     assume "4294967295 < y"
     thus ?case by auto
   next
     assume a1:"y = unat (x - 1)"
     then have "x < x - 1 \<or> x - 1 < x" using sub_wrap_lt by fastforce
     thus ?case
     proof
       assume "x < x - 1" 
       then have "x = 0" by (meson le_less measure_unat not_le word_less_nat_alt)
       then have y1:"x - 1 = 0xFFFFFFFF" by auto
       then have "unat (x - 1) = unat (0xFFFFFFFF::32 word)"  by (simp add: y1)
       then have "y =  4294967295" using a1 max_word32_to_nat by auto
       thus ?case by auto
     next
       assume "x - 1 < x"
       thus ?case
         by (metis a1 Suc.prems Suc_lessI less_irrefl unat_mono word_of_nat_less)
     qed
   qed
 qed
    
lemma of_nat_ltword32max_zero_identity:"y \<le> 4294967295 ==> 0 = (of_nat y::32 word) \<Longrightarrow> 0 = y"
  using of_nat_eq_overflow_or_not  by (metis not_le unat_0)
    
lemma no_overflow_of_nat_identity:"x \<le> 4294967295 \<Longrightarrow> y \<le> 4294967295 ==> of_nat x = (of_nat y::32 word) \<Longrightarrow> x = y"
proof(induct x arbitrary: y)
  case 0
  then show ?case by (auto simp add: of_nat_ltword32max_zero_identity)
next
  case (Suc x)
  then have "y = 0 \<or> 0 < y" by auto
  thus ?case
  proof
    assume "y = 0"
    thus ?case using Suc by (metis of_nat_ltword32max_zero_identity semiring_1_class.of_nat_0)
  next
    assume a1:"0 < y"
    then obtain y' where y1:"y' = y - 1" by auto
    then have y2:"x \<le> 4294967295" using Suc by auto
    then have y3:"y' \<le> 4294967295" using Suc y1 by auto
    then have y4:"x = y'"
      by (metis (no_types) Suc_eq_plus1 UINT_MAX_def a1 add.commute add.left_neutral add_diff_cancel_left' le_less linorder_not_le local.Suc(1) local.Suc(2) local.Suc(4) not_less_eq of_nat_add of_nat_diff y1 y3)
    thus ?case using Suc y1 Suc_diff_1 a1 by blast
  qed
qed

lemma nat_word_ineq:"x < 4294967295 \<Longrightarrow> ((of_nat x::32 word) < 0xFFFFFFFF)"
proof (induct x)
  case 0
  then show ?case by auto
next
  case (Suc x)
  then have y1:"x < 4294967294" by auto
  then have y2:"x < 4294967295" by auto
  then have y3:"((of_nat x::32 word) < 0xFFFFFFFF)" using Suc by auto
  then have "\<And>n. (1::32 word) + numeral (num.Bit0 n) = numeral (num.Bit1 n) + 0"
      by simp
  then have "(of_nat x::32 word) = 0xFFFFFFFE \<or> (of_nat x::32 word) < 0xFFFFFFFE"
      by (metis (no_types)  y3 add.commute add.left_neutral inc_le le_less linorder_not_le)
   thus ?case
   proof
     assume a1:"(of_nat x::32 word) = 0xFFFFFFFE"
     then have "of_nat x = (of_nat 4294967294::32 word)" by auto
     then have "x = 4294967294" using a1 y2 no_overflow_of_nat_identity by auto
     thus ?case using Suc by auto
   next
     assume a1:"(of_nat x::32 word) < 0xFFFFFFFE"
     thus ?case
       by (metis add.commute add_diff_cancel_left' eval_nat_numeral(3) inc_le linorder_not_le of_nat_Suc of_nat_numeral word32_identity1)
   qed
qed

lemma word32_addition_ineq2:"x < UINT_MAX \<Longrightarrow> (p::32 word) \<noteq> p + of_nat x \<or> x = 0"
proof(induct x)
  case 0
  then show ?case by auto
next
  case (Suc x)
  then have y1:"x < UINT_MAX" by auto
  then have "x = 0 \<or> 0 < x" by auto
  thus ?case
  proof
    assume "x = 0"
    then have "p \<noteq> p + of_nat (Suc x)" by auto
    thus ?case by auto
  next
    assume a1:"0 < x"
    then have "p \<noteq> p + of_nat x" using Suc y1 by auto
    then have y2:"p \<noteq> p + of_nat x \<or> x = 0" using Suc y1 by auto
    thus ?case
    proof
      assume "p \<noteq> p + of_nat x"
      have "\<exists>w. of_nat x < (w::32 word)"
          using UINT_MAX_def nat_word_ineq y1 by auto
      thus ?case
        by (metis (no_types)  Suc nat_word_ineq add.commute add_cancel_right_right add_diff_cancel_right' 
            add_uminus_conv_diff of_nat_Suc word_not_simps(3))
    next
      assume "x = 0"
      thus ?case using a1 by blast
    qed
  qed
qed
  
lemma ptr_ushort_offset_equality_is_zero:
  assumes a1:"a \<le> USHORT_MAX"
  and a2:"(p::Waypoint_struct_C ptr) = p +\<^sub>p a"
  shows "a = 0"
proof -
  have y1:"a * size_of TYPE(Waypoint_struct_C) < UINT_MAX" using a1 uxas_array_length_lt_uint_max by fastforce  
  then have "ptr_val p \<noteq> ptr_val p + of_nat a * of_nat (size_of TYPE(Waypoint_struct_C)) \<or> a = 0" using word32_addition_ineq2 
  by fastforce 
  thus ?thesis
  proof
    assume "ptr_val p \<noteq> ptr_val p + of_nat a * of_nat (size_of TYPE(Waypoint_struct_C))" 
    then have "ptr_val p \<noteq> ptr_val p + of_int (int a) * of_nat (size_of TYPE(Waypoint_struct_C))" by auto 
    then have "(Ptr(ptr_val p)::Waypoint_struct_C ptr) \<noteq> Ptr(ptr_val p + of_int (int a) * of_nat (size_of TYPE(Waypoint_struct_C)))" by blast
    then have "(p::Waypoint_struct_C ptr) \<noteq> p +\<^sub>p a" by (simp add: CTypesDefs.ptr_add_def)
    thus ?thesis using a2 by auto
  next
    assume "a = 0"
    thus ?thesis by auto
  qed
qed
  
lemma add_identity:
  assumes a1:" (p::Waypoint_struct_C ptr) +\<^sub>p ((a  + 1)::nat) = p +\<^sub>p (b::nat)"
  shows "p +\<^sub>p int a = p +\<^sub>p (int b - 1)" 
proof -
  have "Ptr(ptr_val p + of_nat (a + 1) * of_nat (size_of TYPE(Waypoint_struct_C))) = Ptr(ptr_val p + of_nat b * of_nat (size_of TYPE(Waypoint_struct_C)))"
    using a1 by (simp add: CTypesDefs.ptr_add_def)
    have "ptr_val p + of_int (int ((1 + a) * size_of (TYPE(Waypoint_struct_C)::Waypoint_struct_C itself))) = ptr_val p + of_int (int (b * size_of (TYPE(Waypoint_struct_C)::Waypoint_struct_C itself)))"
      using \<open>Ptr (ptr_val p + of_nat (a + 1) * of_nat (size_of TYPE(Waypoint_struct_C))) = Ptr (ptr_val p + of_nat b * of_nat (size_of TYPE(Waypoint_struct_C)))\<close> by force
    then have "Ptr(ptr_val p + of_nat a * of_nat (size_of TYPE(Waypoint_struct_C)) + of_nat (size_of TYPE(Waypoint_struct_C))) = Ptr(ptr_val p + of_nat b * of_nat (size_of TYPE(Waypoint_struct_C)))"
      by (metis (no_types) add.commute add.left_commute of_int_of_nat_eq of_nat_add of_nat_mult semiring_normalization_rules(3))
      have f1: "\<And>w wa wb. (w::32 word) + wa + - wb = w + (wa + - wb)"
        by simp
      have f2: "\<And>w wa. (w::32 word) + (wa + - w) = wa"
        by simp
      have f3: "Ptr (ptr_val p + of_nat a * of_nat (size_td (typ_info_t (TYPE(Waypoint_struct_C)::Waypoint_struct_C itself))) + of_nat (size_td (typ_info_t (TYPE(Waypoint_struct_C)::Waypoint_struct_C itself)))) = (Ptr (ptr_val p + of_nat b * of_nat (size_td (typ_info_t (TYPE(Waypoint_struct_C)::Waypoint_struct_C itself))))::Waypoint_struct_C ptr)"
        using \<open>Ptr (ptr_val p + of_nat a * of_nat (size_of TYPE(Waypoint_struct_C)) + of_nat (size_of TYPE(Waypoint_struct_C))) = Ptr (ptr_val p + of_nat b * of_nat (size_of TYPE(Waypoint_struct_C)))\<close> by force
      have f4: "\<And>w wa. - (w::32 word) + - wa = - (w + wa)"
        by simp
      have f5: "\<And>w wa. (w::32 word) + - (wa + w) = - wa"
        by auto
      have "ptr_val p + (of_nat (size_td (typ_info_t (TYPE(Waypoint_struct_C)::Waypoint_struct_C itself))) + of_nat a * of_nat (size_td (typ_info_t (TYPE(Waypoint_struct_C)::Waypoint_struct_C itself)))) = ptr_val p + of_nat b * of_nat (size_td (typ_info_t (TYPE(Waypoint_struct_C)::Waypoint_struct_C itself)))"
        using f3 by (simp add: add.commute)
      then have "of_nat (size_td (typ_info_t (TYPE(Waypoint_struct_C)::Waypoint_struct_C itself))) + (of_nat a * of_nat (size_td (typ_info_t (TYPE(Waypoint_struct_C)::Waypoint_struct_C itself))) + - (ptr_val p + of_nat b * of_nat (size_td (typ_info_t (TYPE(Waypoint_struct_C)::Waypoint_struct_C itself))))) = - ptr_val p"
        using f5 f1 by (metis (no_types))
      then have "of_nat a * of_nat (size_td (typ_info_t (TYPE(Waypoint_struct_C)::Waypoint_struct_C itself))) + - (ptr_val p + (- ptr_val p + of_nat b * of_nat (size_td (typ_info_t (TYPE(Waypoint_struct_C)::Waypoint_struct_C itself))))) = - of_nat (size_td (typ_info_t (TYPE(Waypoint_struct_C)::Waypoint_struct_C itself)))"
        using f5 f4 f1 by (metis (no_types) add.commute)
      then have "ptr_val p + (- ptr_val p + (of_nat b * of_nat (size_td (typ_info_t (TYPE(Waypoint_struct_C)::Waypoint_struct_C itself))) + - of_nat (size_td (typ_info_t (TYPE(Waypoint_struct_C)::Waypoint_struct_C itself))))) = of_nat a * of_nat (size_td (typ_info_t (TYPE(Waypoint_struct_C)::Waypoint_struct_C itself)))"
        using f2 f1 by (metis (no_types))
      then have "Ptr(ptr_val p + of_nat a * of_nat (size_of TYPE(Waypoint_struct_C))) = Ptr(ptr_val p + of_nat b * of_nat (size_of TYPE(Waypoint_struct_C)) - of_nat (size_of TYPE(Waypoint_struct_C)))"
        by simp
      thus ?thesis 
        by (simp add: CTypesDefs.ptr_add_def Waypoint_struct_C_typ_info mult.commute right_diff_distrib size_of_def)
    qed
  
lemma ptr_offset_equality:"a \<le> USHORT_MAX \<Longrightarrow> b \<le> USHORT_MAX  \<Longrightarrow> (p::Waypoint_struct_C ptr) +\<^sub>p a = p +\<^sub>p b \<Longrightarrow> a = b"
proof(induct a arbitrary: b)
  case 0
  then show ?case using ptr_ushort_offset_equality_is_zero by auto
next
  case (Suc a)
  then have y1:"p +\<^sub>p (int a  + 1) = p +\<^sub>p int b" by (metis Suc_eq_plus1 of_nat_1 of_nat_add)
  then have y2:"b = 0 \<or> 0 < b" by auto
  thus ?case
  proof
    assume "b = 0"
    thus ?case by (metis of_nat_eq_0_iff ptr_add_0_id ptr_ushort_offset_equality_is_zero Suc)
  next
    assume a1:"0 < b"
    then have "p +\<^sub>p int a = p +\<^sub>p (int b - 1)" using y1 add_identity by (metis Suc_eq_plus1 local.Suc(4))
    then have "a = b - 1" by (metis Suc One_nat_def Suc_pred a1 linorder_not_le not_less_eq of_nat_1 of_nat_diff order_le_less)
    thus ?case by (simp add: a1)
  qed
qed
  
(* A subset of what we expect a valid mission command to entail. I.E, the ptr to the front
 * of the waypoint pointer array is valid, all elements in that array are valid and all pointers
 * to waypoints are valid. 
 *)     
definition are_valid_Waypoints where 
  "are_valid_Waypoints s wsp (len::nat) \<equiv> 
    is_valid_Waypoint_struct_C s wsp
    \<and> wsp \<noteq> NULL
    \<and> (\<forall> j < len. is_valid_Waypoint_struct_C s (wsp +\<^sub>p j) \<and> wsp +\<^sub>p j \<noteq> NULL) "
  
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