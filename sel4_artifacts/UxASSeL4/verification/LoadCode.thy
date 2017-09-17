theory LoadCode imports 
"/home/dacosta/dev/rc/l4v/tools/autocorres/AutoCorres"
begin

install_C_file "../CMASI/MissionCommandUtils.c"
autocorres[ts_rules = nondet, heap_abs_syntax] "../CMASI/MissionCommandUtils.c"  
  
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
  
definition get_waypoint_number where
  "get_waypoint_number = number_C"

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

lemma [simp]: "number_C = get_waypoint_number" using get_waypoint_number_def by auto
    
(* A subset of what we expect a valid mission command to entail. I.E, the ptr to the front
 * of the waypoint pointer array is valid, all elements in that array are valid and all pointers
 * to waypoints are valid. 
 *)     
definition is_valid_MissionCommand where 
  "is_valid_MissionCommand s mcp \<equiv> 
    is_valid_MissionCommand_struct_C s mcp
    \<and> (\<forall> j < unat (get_waypoints_length s mcp).
        is_valid_Waypoint_struct_C'ptr s (get_waypoint_ptr_ptr s mcp j)
        \<and> is_valid_Waypoint_struct_C s (get_waypoint_ptr s mcp j)
        \<and> get_waypoint_ptr s mcp j \<noteq> NULL)"

(* Generally useful lemma." *)
  
lemma [simp]: "(a::32 word) < n \<Longrightarrow> unat (n - (a + 1)) < unat (n - a)"
proof -
  assume "a < n"
  then have "0 \<noteq> n - a"
    by force
  then show ?thesis
    by (simp add: add.commute diff_add_eq_diff_diff_swap measure_unat)
qed

lemma [simp]: "j < i \<Longrightarrow> int (unat j) = uint j" by (simp add: uint_nat)



end