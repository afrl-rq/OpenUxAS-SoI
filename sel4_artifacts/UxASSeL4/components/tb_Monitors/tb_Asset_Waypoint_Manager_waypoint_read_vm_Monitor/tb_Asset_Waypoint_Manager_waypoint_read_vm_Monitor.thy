(* Verifying proper queue functionality using AutoCorress requires the following
 * two modifications:
 * 1) The line in "src/tb_Asset_Waypoint_Manager_waypoint_read_vm_Monitor.c" defining TB_VERIFY
 *    must be uncommented.
 * 2) The AUTOCORRES_HOME text below must be replaced by the path to the 
 *    AutoCorres package for Isabelle.
 *)
theory tb_Asset_Waypoint_Manager_waypoint_read_vm_Monitor
imports AUTOCORRES_HOME
begin

type_synonym 'a queue = "'a list \<times> nat \<times> nat"

fun wf :: "'a queue \<Rightarrow> bool" where
  "wf (xs, f, n) = (0 < length xs \<and> f < length xs \<and> n \<le> length xs)"

fun is_empty :: "'a queue \<Rightarrow> bool" where
  "is_empty (xs, f, n) = (n = 0)"

fun is_full :: "'a queue \<Rightarrow> bool" where
  "is_full (xs, f, n) = (n = length xs)"

fun enqueue :: "'a queue \<Rightarrow> 'a \<Rightarrow> 'a queue" where
  "enqueue (xs, f, n) x =
    (if \<not>is_full (xs, f, n) then
       (xs[(f + n) mod length xs := x], f, n + 1)
     else
       undefined)"

fun dequeue :: "'a queue \<Rightarrow> 'a \<times> 'a queue" where
  "dequeue (xs, f, Suc n) = (xs!f, (xs, (f + 1) mod length xs, n))" |
  "dequeue (xs, f, 0) = undefined"

fun rep :: "'a queue \<Rightarrow> 'a list" where
  "rep (xs, f, n) = take n (rotate f xs)"

lemma enqueue_wf[intro, simp]:
  "\<lbrakk> wf q; \<not>is_full q \<rbrakk> \<Longrightarrow> wf (enqueue q x)"
by (cases q, auto)

lemma dequeue_wf[intro, simp]:
  "\<lbrakk> wf q; \<not>is_empty q \<rbrakk> \<Longrightarrow> wf (snd (dequeue q))"
by (cases q, auto simp: gr0_conv_Suc)

lemma nth_rotate1:
  "i < length xs \<Longrightarrow> rotate1 xs ! i = (if Suc i < length xs then xs ! (Suc i) else xs ! 0)"
by (cases "xs = []", auto simp: rotate1_hd_tl nth_append nth_tl hd_conv_nth)

lemma nth_rotate1_mod:
  "0 < length xs \<Longrightarrow> rotate1 xs ! (i mod length xs) = xs ! (Suc i mod length xs)"
by (metis hd_rotate_conv_nth length_greater_0_conv length_rotate1 rotate1_rotate_swap rotate_Suc)

lemma rotate1_Suc_update:
  "rotate1 (xs[Suc n mod length xs := x]) = (rotate1 xs)[n mod length xs := x]"
by (cases "xs = []", auto simp: mod_Suc nth_list_update nth_rotate1 intro: nth_equalityI)

lemma rotate_update:
  "rotate f (xs[(f + n) mod length xs := x]) = rotate f xs[n mod length xs := x]"
by (induction f arbitrary: n, simp_all, metis rotate1_Suc_update length_rotate add_Suc_right)

lemma nth_rotate:
  "n < length xs \<Longrightarrow> (rotate f xs) ! n = xs ! ((f + n) mod length xs)"
by (induction f arbitrary: xs, auto simp: rotate1_rotate_swap nth_rotate1_mod length_ineq_not_Nil)

lemma enqueue_rep:
  "\<lbrakk> wf q; \<not>is_full q \<rbrakk> \<Longrightarrow> rep (enqueue q x) = rep q @ [x]"
by (cases q, auto simp: take_Suc_conv_app_nth rotate_update nth_rotate)

lemma dequeue_rep:
  "\<lbrakk> wf q; \<not>is_empty q; dequeue q = (x, q') \<rbrakk> \<Longrightarrow> rep q = x # rep q'"
apply (cases q, simp)
apply (auto simp: gr0_conv_Suc take_Suc hd_rotate_conv_nth rotate_conv_mod[symmetric] rotate1_hd_tl)
done


install_C_file "src/tb_Asset_Waypoint_Manager_waypoint_read_vm_Monitor.c"
autocorres[ts_rules = nondet, heap_abs_syntax] "src/tb_Asset_Waypoint_Manager_waypoint_read_vm_Monitor.c"

context tb_Asset_Waypoint_Manager_waypoint_read_vm_Monitor begin

lemma monsig_emit_wp [wp]:
  "\<lbrace> P \<rbrace>
   monsig_emit'
   \<lbrace> \<lambda>_. P \<rbrace>!"
  sorry

lemma mon_get_sender_id_wp[wp]:
  "\<lbrace> \<lambda> s.  P r s \<rbrace>
   mon_get_sender_id'
   \<lbrace> P \<rbrace>!"
  sorry

definition is_queue :: "lifted_globals \<Rightarrow> bool" where
  "is_queue s \<equiv> front_'' s < 1 \<and> length_'' s \<le> 1"

definition the_queue :: "lifted_globals \<Rightarrow> 32 word queue" where
  "the_queue s \<equiv> (list_array (contents_'' s), unat (front_'' s), unat (length_'' s))"

fun queue_length :: "'a queue \<Rightarrow> nat" where
  "queue_length (xs, f, n) = n"

lemma is_full_wp [wp]:
"\<lbrace> \<lambda>s. if queue_length (the_queue s) = 1 then Q 1 s else Q 0 s \<rbrace>
  is_full'
 \<lbrace> \<lambda>r s. Q r s \<rbrace>!"
  apply (unfold is_full'_def)
  apply wp
  apply (auto simp: the_queue_def unat_arith_simps)
  done

lemma is_empty_wp [wp]:
"\<lbrace> \<lambda>s. if queue_length (the_queue s) = 0 then Q 1 s else Q 0 s \<rbrace>
  is_empty'
 \<lbrace> \<lambda>r s. Q r s \<rbrace>!"
  apply (unfold is_empty'_def)
  apply wp
  apply (auto simp: the_queue_def unat_arith_simps)
  done

lemma enqueue_full:
  "\<lbrace> \<lambda>s. is_queue s \<and> queue_length (the_queue s) = 1 \<and> P s\<rbrace>
   mon_enqueue' x
   \<lbrace> \<lambda>r s. r = 0 \<and> P s\<rbrace>!"
  apply (rule validNF_assume_pre)
  apply (unfold mon_enqueue'_def)
  apply wp 
  apply auto
  done

lemma list_array_update:
"i < length (list_array a) \<Longrightarrow> list_array (Arrays.update a i x) = list_array a[i := x]"
by (auto simp add: list_array_def nth_list_update intro: nth_equalityI)

lemma enqueue_not_full:
  "(\<And>s c. P (s\<lparr>contents_'' := c\<rparr>) = P s) \<Longrightarrow>
   (\<And>s n. P (s\<lparr>length_'' := n\<rparr>) = P s) \<Longrightarrow>
   \<lbrace> \<lambda>s. is_queue s \<and>
         q = the_queue s \<and>
         queue_length q < 1 \<and>
         is_valid_w32 s x \<and>
         P s \<rbrace>
   mon_enqueue' x
   \<lbrace> \<lambda>r s. r = 1 \<and>
           the_queue s = enqueue q (heap_w32 s x) \<and>
           is_queue s \<and>
           P s \<rbrace>!"
apply (unfold mon_enqueue'_def)
apply wp
apply (auto simp: is_queue_def the_queue_def list_array_update unat_arith_simps)
done

lemma dequeue_empty:
  "\<lbrace> \<lambda>s. is_queue s \<and> queue_length (the_queue s) = 0 \<and> P s \<rbrace>
   mon_dequeue' x
   \<lbrace> \<lambda>r s. r = 0 \<and> P s \<rbrace>!"
apply (unfold mon_dequeue'_def)
apply wp
apply (auto simp: is_queue_def the_queue_def unat_arith_simps)
done

lemma dequeue_not_empty:
  "(\<And>s f. P (s\<lparr>front_'' := f\<rparr>) = P s) \<Longrightarrow>
   (\<And>s n. P (s\<lparr>length_'' := n\<rparr>) = P s) \<Longrightarrow>
   (\<And>s v. P (s[x := v]) = P s) \<Longrightarrow>
   (\<And>s v. front_'' (s[x := v]) = front_'' s) \<Longrightarrow>
   (\<And>s v. front_'' (s[x := v]) = length_'' s) \<Longrightarrow>
   \<lbrace> \<lambda>s. is_queue s \<and>
         q = the_queue s \<and>
         queue_length q > 0 \<and>
         is_valid_w32 s x \<and>
         P s \<rbrace>
   mon_dequeue' x
   \<lbrace> \<lambda>r s. r > 0 \<and>
           dequeue q = (heap_w32 s x, the_queue s) \<and>
           is_queue s \<and>
           P s \<rbrace>!"
apply (unfold mon_dequeue'_def)
  apply wp
  apply (metis (mono_tags, hide_lams) fun_upd_def is_queue_def the_queue_def tb_Asset_Waypoint_Manager_waypoint_read_vm_Monitor.heap_w32_update_def
                  gr0_conv_Suc list_array_nth  lifted_globals.simps(3) lifted_globals.simps(4) not_less)
done

end
end
