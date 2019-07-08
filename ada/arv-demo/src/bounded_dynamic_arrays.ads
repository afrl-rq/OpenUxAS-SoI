generic
   type Component is private;
   type List_Index is range <>;
   type List is array (List_Index range <>) of Component;
   Default_Value : Component;
   with function "=" (Left, Right : List) return Boolean is <>;
package Bounded_Dynamic_Arrays is
   pragma Pure;

   Maximum_Length : constant List_Index := List_Index'Last;
   --  The physical maximum for the upper bound of the wrapped List array
   --  values.  Defined for readability in predicates.

   subtype Natural_Index is List_Index'Base range 0 .. Maximum_Length;

   subtype Index is List_Index range 1 .. Maximum_Length;
   --  The representation internally uses a one-based array, hence the
   --  predicate on the generic formal List_Index integer type.

   type Sequence (Capacity : Natural_Index) is private
     with Default_Initial_Condition => Empty (Sequence);
   --  A wrapper for List array values in which Capacity represents the
   --  physical upper bound. Capacity is, therefore, the maximum number of
   --  Component values possibly contained by the associated Sequence instance.
   --  However, not all of the physical capacity of a Sequence need be used at
   --  any moment, leading to the notion of a logical current length ranging
   --  from zero to Capacity.

   Null_List : constant List (List_Index'First .. List_Index'First - 1) := (others => Default_Value);

   function Null_Sequence
   return Sequence
   with
     Post => Null_Sequence'Result.Capacity = 0 and
             Length (Null_Sequence'Result) = 0 and
             Value (Null_Sequence'Result) = Null_List and
             Null_Sequence'Result = Null_List;

   function Instance
     (Content : List)
   return Sequence
   with
     Pre  => Content'Length <= Maximum_Length,
     Post => Length (Instance'Result) = Content'Length and
             Value (Instance'Result) = Content and
             Instance'Result = Content and
             Instance'Result.Capacity = Content'Length and
             Contains (Instance'Result, Content),
     Global  => null,
     Depends => (Instance'Result => Content);

   function Instance
     (Capacity : Natural_Index;
      Content  : Component)
   return Sequence
   with
     Pre  => Capacity >= 1,
     Post => Length (Instance'Result) = 1 and
             Value (Instance'Result) (1) = Content and
             Instance'Result.Capacity = Capacity and
             Instance'Result = Content and
             Contains (Instance'Result, Content),
     Global  => null;
--       Depends => (Instance'Result => (Capacity, Content));

   function Instance
     (Capacity : Natural_Index;
      Content  : List)
   return Sequence
   with
     Pre  => Content'Length <= Capacity,
     Post => Instance'Result.Capacity = Capacity and
             Length (Instance'Result) = Content'Length and
             Value (Instance'Result) = Content and
             Instance'Result = Content and
             Contains (Instance'Result, Content),
     Global  => null;
--       Depends => (Instance'Result => (Capacity, Content));

   function Value (This : Sequence) return List with
     Post => Value'Result'Length = Length (This) and
             Value'Result'First = 1 and
             Value'Result'Last = Length (This),
     Inline;
   --  Returns the content of this sequence. The value returned is the
   --  "logical" value in that only that slice which is currently assigned
   --  is returned, as opposed to the entire physical representation.

   function Value (This : Sequence; Position : Index) return Component with
     Pre => Position in 1 .. Length (This),
     Inline;

   function Length (This : Sequence) return Natural_Index with
     Inline;
   --  Returns the logical length of This, i.e., the length of the slice of
   --  This that is currently assigned a value.

   function Empty (This : Sequence) return Boolean with
     Post=> Empty'Result = (Length (This) = 0),
     Inline;

   procedure Clear (This : out Sequence) with
     Post    => Empty (This) and
                Length (This) = 0 and
                Value (This) = Null_List and
                This = Null_Sequence,
     Global  => null,
     Depends => (This => This),
     Inline;

   procedure Copy (Source : Sequence; To : in out Sequence) with
     Pre  => To.Capacity >= Length (Source),
     Post => Value (To) = Value (Source) and
             Length (To) = Length (Source) and
             To = Source and
             Contains_At (To, 1, Source),
     Global => null,
     Depends => (To =>+ Source);
   --  Copies the logical value of Source, the RHS, to the LHS sequence To. The
   --  prior value of To is lost.

   procedure Copy (Source : List; To : in out Sequence) with
     Pre  => To.Capacity >= Source'Length,
     Post => Value (To) = Source and then
             Length (To) = Source'Length and then
             To = Source and then
             Contains_At (To, 1, Source),
     Global => null,
     Depends => (To =>+ Source);
   --  Copies the value of the array Source, the RHS, to the LHS sequence To.
   --  The prior value of To is lost.

   procedure Copy (Source : Component; To : in out Sequence) with
     Pre  => To.Capacity > 0,
     Post => Value (To) (1) = Source and
             Length (To) = 1 and
             To = Source and
             Contains_At (To, 1, Source),
     Global => null,
     Depends => (To =>+ Source);
   --  Copies the value of the individual array component Source, the RHS, to
   --  the LHS sequence To. The prior value of To is lost.

   overriding
   function "=" (Left, Right : Sequence) return Boolean with
     Inline;

   function "=" (Left : Sequence;  Right : List) return Boolean with
     Inline;

   function "=" (Left : List;  Right : Sequence) return Boolean with
     Inline;

   function "=" (Left : Sequence;  Right : Component) return Boolean with
     Inline;

   function "=" (Left : Component;  Right : Sequence) return Boolean with
     Inline;

   function Normalized (L : List) return List with
     Pre  => L'Length <= Maximum_Length,
     Post => Normalized'Result'First = 1 and
             Normalized'Result'Last = L'Length and
             Normalized'Result = L;
   --  Slides the input into a 1-based array

   function "&" (Left : Sequence; Right : Sequence) return Sequence with
     Pre  => Length (Left) <= Maximum_Length - Length (Right),
     Post => Value ("&"'Result) = Value (Left) & Value (Right) and
             Value ("&"'Result)'First = 1 and
             Length ("&"'Result) = Length (Left) + Length (Right) and
             "&"'Result.Capacity = Length (Left) + Length (Right);

   function "&" (Left : Sequence; Right : List) return Sequence with
     Pre  => Length (Left) <= Maximum_Length - Right'Length,
     Post => Value ("&"'Result) = Value (Left) & Right and
             Value ("&"'Result)'First = 1 and
             Length ("&"'Result) = Length (Left) + Right'Length and
             "&"'Result.Capacity = Length (Left) + Right'Length;

   function "&" (Left : List; Right : Sequence) return Sequence with
     Pre  => Left'Length <= Maximum_Length - Length (Right),
     Post => Value ("&"'Result) = Normalized (Left) & Value (Right) and
             Value ("&"'Result)'First = 1 and
             Length ("&"'Result) = Left'Length + Length (Right) and
             "&"'Result.Capacity = Left'Length + Length (Right);

   function "&" (Left : Sequence; Right : Component) return Sequence with
     Pre  => Length (Left) <= Maximum_Length - 1,
     Post => Value ("&"'Result) = Value (Left) & Right and
             Value ("&"'Result)'First = 1 and
             Length ("&"'Result) = Length (Left) + 1 and
             "&"'Result.Capacity = Length (Left) + 1;

   function "&" (Left : Component; Right : Sequence) return Sequence with
     Pre  => Length (Right) <= Maximum_Length - 1,
     Post => Value ("&"'Result) = Left & Value (Right) and
             Value ("&"'Result)'First = 1 and
             Length ("&"'Result) = 1 + Length (Right) and
             "&"'Result.Capacity = 1 + Length (Right);

   procedure Append (Tail : Sequence; To : in out Sequence) with
     Pre  => Length (Tail) <= To.Capacity - Length (To),
     Post => Value (To) = Value (To'Old) & Value (Tail) and
             Length (To) = Length (To'Old) + Length (Tail); -- and
--               To = Value (To'Old) & Value (Tail);  -- caused crash...

   procedure Append (Tail : List; To : in out Sequence) with
     Pre  => Tail'Length <= To.Capacity - Length (To),
     Post => Value (To) = Value (To'Old) & Tail and
             Length (To) = Length (To'Old) + Tail'Length;

   procedure Append (Tail : Component; To : in out Sequence) with
     Pre  => Length (To) <= To.Capacity - 1,
     Post => Value (To) = Value (To'Old) & Tail and
             Length (To) = Length (To'Old) + 1;

   procedure Amend
     (This  : in out Sequence;
      By    : Sequence;
      Start : Index)
   with
     Pre  => Start <= Length (This) and
             Start - 1 in 1 .. This.Capacity - Length (By) and
             Start <= Maximum_Length - Length (By),
     Post => Value (This) (Start .. Start + Length (By) - 1) = Value (By) and
             (if Start + Length (By) - 1 > Length (This'Old)
                then Length (This) = Start + Length (By) - 1
                else Length (This) = Length (This'Old)) and
             Contains_At (This, Start, By) and
             Unchanged (This'Old, This, Start, Length (By)),
     Global => null,
     Depends => (This =>+ (By, Start));
   --  Overwrites the content of This, beginning at Start, with the logical
   --  value of the Sequence argument By

   procedure Amend
     (This  : in out Sequence;
      By    : List;
      Start : Index)
   with
     Pre  => Start <= Length (This) and
             Start - 1 in 1 .. This.Capacity - By'Length and
             Start <= Maximum_Length - By'Length,
     Post => Value (This) (Start .. Start + By'Length - 1) = By and
             (if Start + By'Length - 1 > Length (This'Old)
                then Length (This) = Start + By'Length - 1
                else Length (This) = Length (This'Old)) and
             Contains_At (This, Start, By) and
             Unchanged (This'Old, This, Start, By'Length),
     Global => null,
     Depends => (This =>+ (By, Start));
   --  Overwrites the content of This, beginning at Start, with the value of
   --  List argument By

   procedure Amend
     (This  : in out Sequence;
      By    : Component;
      Start : Index)
   with
     Pre  => Start <= Length (This) and
             Start <= Maximum_Length - 1,
     Post => Value (This) (Start) = By and
             Length (This) = Length (This)'Old and
             Contains_At (This, Start, By) and
             Unchanged (This'Old, This, Start, 1),
     Global => null,
     Depends => (This =>+ (By, Start));
   --  Overwrites the content of This, at position Start, with the value of
   --  the single Component argument By

   function Location (Fragment : Sequence; Within : Sequence) return Natural_Index with
     Pre  => Length (Fragment) > 0,
     Post => Location'Result in 0 .. Within.Capacity and
             (if Length (Fragment) > Within.Capacity then Location'Result = 0) and
             (if Length (Fragment) > Length (Within) then Location'Result = 0) and
             (if Location'Result > 0 then Contains_At (Within, Location'Result, Fragment));
   --  Returns the starting index of the logical value of the sequence Fragment
   --  in the sequence Within, if any. Returns 0 when the fragment is not
   --  found.
   --  NB: The implementation is not the best algorithm...

   function Location (Fragment : List; Within : Sequence) return Natural_Index with
     Pre  => Fragment'Length > 0,
     Post => Location'Result in 0 .. Length (Within) and
             (if Fragment'Length > Within.Capacity then Location'Result = 0) and
             (if Fragment'Length > Length (Within) then Location'Result = 0) and
             (if Location'Result > 0 then Contains_At (Within, Location'Result, Fragment));
   --  Returns the starting index of the value of the array Fragment in the
   --  sequence Within, if any. Returns 0 when the fragment is not found.
   --  NB: The implementation is a simple linear search...

   function Location (Fragment : Component; Within : Sequence) return Natural_Index with
     Post => Location'Result in 0 .. Length (Within) and
             (if Location'Result > 0 then Contains_At (Within, Location'Result, Fragment));
   --  Returns the index of the value of the component Fragment within the
   --  sequence Within, if any. Returns 0 when the fragment is not found.

   function Contains (Within : Sequence; Fragment : Component) return Boolean with
     Inline;

   function Contains (Within : Sequence; Fragment : List) return Boolean with
     Pre  => Length (Within) - Fragment'Length <= Maximum_Length - 1,
     Post => (if Fragment'Length = 0 then Contains'Result) and
             (if Fragment'Length > Length (Within) then not Contains'Result),
     Inline;

   function Contains (Within : Sequence; Fragment : Sequence) return Boolean with
     Pre  => Length (Within) - Length (Fragment) <= Maximum_Length - 1,
     Post => (if Length (Fragment) = 0 then Contains'Result) and
             (if Length (Fragment) > Length (Within) then not Contains'Result),
     Inline;

   function Contains_At
     (Within   : Sequence;
      Start    : Index;
      Fragment : Sequence)
   return Boolean
   with Inline;

   function Contains_At
     (Within   : Sequence;
      Start    : Index;
      Fragment : List)
   return Boolean;
--     with Inline,
--          Pre => Start <= Length (Within) and then
--                 Start - 1 <= Length (Within) - Fragment'Length;

   function Contains_At
     (Within   : Sequence;
      Position : Index;
      Fragment : Component)
   return Boolean
   with Inline;

   function Unchanged
     (Original     : Sequence;
      Current      : Sequence;
      Slice_Start  : Index;
      Slice_Length : Natural_Index)
   return Boolean
   --  Returns whether the Original content is the same as the Current content,
   --  except for the slice beginning at Slice_Start and having Slice_Length
   --  number of components.
   with
     Pre => Original.Capacity = Current.Capacity and
            Slice_Start <= Length (Original) and
            Slice_Start - 1 <= Original.Capacity - Slice_Length and
            Slice_Start <= Maximum_Length - Slice_Length,
     Ghost;

private

   type Sequence (Capacity : Natural_Index) is record
      Current_Length : Natural_Index := 0;
      Content        : List (1 .. Capacity) := (others => Default_Value);
   end record
     with Predicate => Current_Length in 0 .. Capacity;

   ------------
   -- Length --
   ------------

   function Length (This : Sequence) return Natural_Index is
     (This.Current_Length);

   -----------
   -- Value --
   -----------

   function Value (This : Sequence) return List is
     (This.Content (1 .. This.Current_Length));

   -----------
   -- Value --
   -----------

   function Value (This : Sequence; Position : Index) return Component is
     (This.Content (Position));

   -----------
   -- Empty --
   -----------

   function Empty (This : Sequence) return Boolean is
     (This.Current_Length = 0);

   --------------
   -- Contains --
   --------------

   function Contains (Within : Sequence; Fragment : Component) return Boolean is
     (for some K in 1 .. Length (Within) =>
        Within.Content (K) = Fragment);

   -----------------
   -- Contains_At --
   -----------------

   function Contains_At
     (Within   : Sequence;
      Start    : Index;
      Fragment : List)
   return Boolean
   is
      ((Start - 1 <= Within.Current_Length - Fragment'Length)
      and then
      Within.Content (Start .. (Start + Fragment'Length - 1)) = Fragment);
   --  note that this includes the case of a null slice on each side, eg
   --  when Start = 1 and Fragment'Length = 0, which is intended to return
   --  True

   -----------------
   -- Contains_At --
   -----------------

   function Contains_At
     (Within   : Sequence;
      Start    : Index;
      Fragment : Sequence)
   return Boolean
   is
     (Contains_At (Within, Start, Value (Fragment)));

   -----------------
   -- Contains_At --
   -----------------

   function Contains_At
     (Within   : Sequence;
      Position : Index;
      Fragment : Component)
   return Boolean
   is
     (Position in 1 .. Within.Current_Length
      and then
      Within.Content (Position) = Fragment);

   --------------
   -- Contains --
   --------------

   function Contains (Within : Sequence; Fragment : List) return Boolean is
      --  We want to return True when the fragment is empty (eg "") because we
      --  want to use Contains in the postcondition to Instance, and we want to
      --  allow creating an instance that is empty (because "&" can work with
      --  empty fragments/instances). Therefore we must allow a zero length
      --  Fragment.
      --
      --  Also, note that we need to explicitly check for the empty fragment
      --  (using the short-circuit form) because otherwise the expression
      --  "(Within.Current_Length - Fragment'Length + 1)" would go past the
      --  current length.
     (Fragment'Length = 0
      or else
      --  But also, for Within to possibly contain the slice Fragment,
      --  the length of the fragment cannot be greater than the length
      --  of Within.Content.
      (Fragment'Length in 1 .. Within.Current_Length
       and then
       (for some K in Within.Content'First .. (Within.Current_Length - Fragment'Length + 1) =>
           Contains_At (Within, K, Fragment))));

   --------------
   -- Contains --
   --------------

   function Contains (Within : Sequence; Fragment : Sequence) return Boolean is
     (Contains (Within, Value (Fragment)));

   ---------------
   -- Unchanged --
   ---------------

   function Unchanged
     (Original     : Sequence;
      Current      : Sequence;
      Slice_Start  : Index;
      Slice_Length : Natural_Index)
   return Boolean
   is
      --  First we verify the part before the ammended slice, if any. If there
      --  is none before, this will compare against a null slice and so will
      --  return True.
      (Current.Content (1 .. Slice_Start - 1) = Original.Content (1 .. Slice_Start - 1)
      and then
      --  Now we verify the part after the ammended slice, if any, but also
      --  noting that the ammended part might extend past the end of the
      --  original. In other words, ammending a sequence can extend the
      --  length of the original.
      Current.Content (Slice_Start + Slice_Length .. Original.Current_Length) =
                   Original.Content (Slice_Start + Slice_Length .. Original.Current_Length));

   ---------
   -- "=" --
   ---------

   overriding
   function "=" (Left, Right : Sequence) return Boolean is
     (Value (Left) = Value (Right));

   ---------
   -- "=" --
   ---------

   function "=" (Left : Sequence;  Right : List) return Boolean is
     (Value (Left) = Right);

   ---------
   -- "=" --
   ---------

   function "=" (Left : List;  Right : Sequence) return Boolean is
     (Right = Left);

   ---------
   -- "=" --
   ---------

   function "=" (Left : Sequence;  Right : Component) return Boolean is
      (Left.Current_Length = 1 and then Left.Content (1) = Right);

   ---------
   -- "=" --
   ---------

   function "=" (Left : Component;  Right : Sequence) return Boolean is
     (Right = Left);

end Bounded_Dynamic_Arrays;
