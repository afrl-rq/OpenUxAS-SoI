(* Verifying proper queue functionality using AutoCorress requires the following
 * two modifications:
 * 1) The AUTOCORRES_HOME text below must be replaced by the path to the 
 *    AutoCorres package for Isabelle.
 * 2) The line in "src/tb_ping_i_Monitor.c" defining TB_VERIFY
 *    must be uncommented.
 *)
theory tb_Waypoint_Manager_mission_write_Monitor
imports AUTOCORRES_HOME
begin


install_C_file "src/tb_Waypoint_Manager_mission_write_Monitor.c"
autocorres[ts_rules = nondet, heap_abs_syntax] "src/tb_Waypoint_Manager_mission_write_Monitor.c"

context tb_Waypoint_Manager_mission_write_Monitor begin

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

lemma is_full_wp [wp]:
"\<lbrace> \<lambda>s. if  (length_'' s) = 1 then Q 1 s else Q 0 s \<rbrace>
  is_full'
 \<lbrace> \<lambda>r s. Q r s \<rbrace>!"
  apply (unfold is_full'_def)
  apply wp
  apply (auto simp: unat_arith_simps)
  done

lemma is_empty_wp [wp]:
"\<lbrace> \<lambda>s. if  (length_'' s) = 0 then Q 1 s else Q 0 s \<rbrace>
  is_empty'
 \<lbrace> \<lambda>r s. Q r s \<rbrace>!"
  apply (unfold is_empty'_def)
  apply wp
  apply (auto simp: unat_arith_simps)
  done

lemma enqueue_full:
  "\<lbrace> \<lambda>s. (length_'' s) = 1 \<and> P s\<rbrace>
   mon_enqueue'
   \<lbrace> \<lambda>r s. r = 0 \<and> P s\<rbrace>!"
  apply (rule validNF_assume_pre)
  apply (unfold mon_enqueue'_def)
  apply wp 
  apply auto
  done

lemma enqueue_not_full:
  "(\<And>s n. P (s\<lparr>length_'' := n\<rparr>) = P s) \<Longrightarrow>
   \<lbrace> \<lambda>s. (length_'' s) = n \<and> n < 1 \<and> P s \<rbrace>
   mon_enqueue'
   \<lbrace> \<lambda>r s. r = 1  \<and> P s \<and> (length_'' s) = n + 1 \<rbrace>!"
apply (unfold mon_enqueue'_def)
  apply wp
  apply auto
done 

lemma dequeue_empty:
  "\<lbrace> \<lambda>s. (length_'' s) = 0 \<and> P s \<rbrace>
   mon_dequeue'
   \<lbrace> \<lambda>r s. r = 0 \<and> P s \<rbrace>!"
apply (unfold mon_dequeue'_def)
apply wp
apply  auto
done

lemma dequeue_not_empty:
  "(\<And>s n. P (s\<lparr>length_'' := n\<rparr>) = P s) \<Longrightarrow>
   \<lbrace> \<lambda>s. (length_'' s) = n \<and> n > 0 \<and> P s \<rbrace>
   mon_dequeue'
   \<lbrace> \<lambda>r s. r > 0 \<and>  (length_'' s) = n - 1 \<and> P s \<rbrace>!"
apply (unfold mon_dequeue'_def)
  apply wp
  apply auto
done

end
end
