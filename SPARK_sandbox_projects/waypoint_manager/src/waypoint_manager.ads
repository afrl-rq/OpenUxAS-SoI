package waypoint_manager with SPARK_Mode is

   type waypoint is record
      id   : positive;
      next : positive;
      valid: boolean;
   end record;

   invalid_waypoint: constant waypoint := waypoint'(id => 1, next => 1, valid => false);

   subtype waypoint_list_index is natural range 0 .. 2**16 - 1;
   type waypoint_list is array (waypoint_list_index range <>) of waypoint;

   function valid(wp: waypoint) return boolean is
      (wp.valid)
   with Ghost;

   function valid(wp_list: waypoint_list) return boolean is
      (for all i in wp_list'Range => valid(wp_list(i)))
   with Ghost;

   -- A well-formed list is one such that all next ids correspond to an id
   -- somewhere in the list
   function well_formed(wp_list: waypoint_list) return boolean is
     (for all i in wp_list'Range =>
        (for some j in wp_list'Range =>
                 wp_list(j).id = wp_list(i).next))
   with Ghost;

   -- A well-formed slice is one such that all next ids in the *slice*
   -- correspond to an id somewhere in the *full* list
   function well_formed(wp_list: waypoint_list; last: natural) return boolean is
     (for all i in wp_list'First .. last =>
        (for some j in wp_list'Range =>
              wp_list(j).id = wp_list(i).next))
   with Pre => (last <= wp_List'Last),
   Ghost;

   -- An in-order list is one such that each next ids point to the id of the
   -- next element in the array
   function in_order(wp_list: waypoint_list) return boolean is
      (for all i in wp_list'First .. wp_list'Last - 1 =>
            wp_list(i).next = wp_list(i + 1).id)
   with Pre => wp_list'Length > 0,
   Ghost;

   -- We are interested in finding the first waypoint in the list with the
   -- desired id, so this is for checking if a waypoint is the first waypoint in
   -- a list with its id
   function is_first_with_id(wp: waypoint; wp_list: waypoint_list) return boolean is
     (for some i in wp_list'Range =>
        -- This waypoint is in the list at some point
        (wp = wp_list(i) and
        -- There is no waypoint before this point that has the id of wp
        (for all j in wp_list'First .. i - 1 =>
                 wp_list(j).id /= wp.id)))
   with Ghost;

   -- Does a waypoint's next waypoint refer back to itself?
   function waypoint_self_cycles(wp: waypoint) return boolean is
      (wp.next = wp.id)
   with Ghost;

   function subset_ids(subset_list: waypoint_list; wp_list: waypoint_list) return boolean is
     (for all i in subset_list'Range =>
        (for some j in wp_list'Range =>
                 subset_list(i).id = wp_list(j).id))
   with Ghost;

   function subset_from_first(subset_list: waypoint_list; wp_list: waypoint_list) return boolean is
     (for all i in subset_list'Range =>
        -- This element from the subset exists in the bigger list and
        -- it is the first element of the bigger list with that id
           is_first_with_id(subset_list(i), wp_list))
   with Ghost;

   function find_wp(waypoint_id: positive; wp_list: waypoint_list) return waypoint
     with
      Pre => valid(wp_list),
      Post => ((if valid(find_wp'Result) then
                -- if the waypoint is found, it should have the desired id
                 (find_wp'Result.id = waypoint_id and
                -- if the waypoint is found, it should be the first one with its id
                  is_first_with_id(find_wp'Result, wp_list))
                -- if the waypoint is not found, there should be no waypoint in the
                -- list with the desired id
               else
                   (for all i in wp_list'Range =>
                      wp_list(i).id /= waypoint_id)));

   function fill_win(wp_list: waypoint_list; starter_id: positive; len: positive) return waypoint_list
     with
       Pre =>
         -- the source waypoint list cannot have any invalid waypoints
         valid(wp_list) and
         -- the waypoint list to generate should be no bigger than the source
         -- waypoint list
         len <= wp_list'Length and
         -- all next ids in the source waypoint list correspond to ids in the
         -- source waypoint list
         well_formed(wp_list) and
         -- the starter id can be found in the source waypoint list
         (for some j in wp_list'Range => wp_list(j).id = starter_id),
      Post =>
         -- Post1: the generated waypoint list cannot have any invalid waypoints
         valid(fill_win'Result) and
         -- Post2: the first waypoint corresponds to the starter id
         (fill_win'Result(fill_win'Result'First).id = starter_id) and
         -- Post3: the last waypoint self-cycles
         waypoint_self_cycles(fill_win'Result(fill_win'Result'Last)) and
         -- Post4: all next ids in the generated waypoint list correspond to ids
         -- in previous element of the generated waypoint list
         in_order(fill_win'Result) and
         -- Post5: all ids in the generated waypoint list can be found in the
         -- source waypoint list
         subset_ids(fill_win'Result, wp_list) and
         -- Post6: all generated waypoints but the last one match exactly a
         -- waypoint from the source waypoint list (and that match is the first
         -- one in the source waypoint list)
         subset_from_first(fill_win'Result(fill_win'Result'First ..
                                           fill_win'Result'Last - 1),
                           wp_list) and
         -- Post7: The window is of the correct size
         fill_win'Result'Length = len and
         -- Post8: all next ids in the generated waypoint list correspond to ids
         -- in the generated waypoint list
         well_formed(fill_win'Result) and
         -- Post9: The window is a zero-based array
         fill_win'Result'First = 0;

end waypoint_manager;
