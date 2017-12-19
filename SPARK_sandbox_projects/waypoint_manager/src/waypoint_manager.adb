Package body waypoint_manager with SPARK_Mode is

   function find_wp(waypoint_id: positive; wp_list: waypoint_list) return waypoint
   is
   begin
      for i in wp_list'Range
      loop
         if wp_list(i).id = waypoint_id then
            return wp_list(i);
         end if;
         pragma Loop_Invariant(for all j in wp_list'First .. i =>
                                 wp_list(j).id /= waypoint_id);
      end loop;
      return invalid_waypoint;
   end find_wp;

   function fill_win(wp_list: waypoint_list; starter_id: positive;
                     len    : positive) return waypoint_list
   is
      retval: waypoint_list(0 .. len-1) := (others => invalid_waypoint);
      next_id: positive := starter_id;
   begin
      for i in retval'Range
      loop
         retval(i) := find_wp(next_id, wp_list);
         next_id := retval(i).next;
         -- Post1
         pragma Loop_Invariant(valid(retval(retval'First .. i)));
         -- Post2
         pragma Loop_Invariant(retval(retval'First).id = starter_id);
         ---------
         -- Post4
         pragma Loop_Invariant(next_id = retval(i).next);
         pragma Loop_Invariant(in_order(retval(retval'First .. i)));
         ---------
         -- Post5
         pragma Loop_Invariant(subset_ids(retval(retval'First .. i), wp_list));
         ---------
         -- Post6
         pragma Loop_Invariant(subset_from_first(retval(retval'First .. i), wp_list));
         ---------
      end loop;
      -- Post3 (and helps Post8)
      retval(retval'Last).next := retval(retval'Last).id;
      -- The following pragma assert cuts the proof tie from about 1 minute to
      -- about 15-18 seconds
      pragma Assert(in_order(retval));
      return retval;
   end fill_win;

end waypoint_manager;
