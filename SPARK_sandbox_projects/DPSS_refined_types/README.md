DPSS_refined_types
================================================================================

This SPARK Ada project further revises the implementation of DPSS found in
`../DPSS_position_input`. This implementation adds type constraints and type
predicates wherever possible to reduce the number of preconditions and
postconditions needed to ensure consistency and to enable proof.

Also in this revision, the LEFT and RIGHT constants for direction have been
used throughout UAV_Pkg. These constants were defined in the AGREE but were not
used.

Unused types and constants have been removed in this version. 

# Proof #

All directly stated properties prove automatically at level 2, e.g., using the
following command:

      gnatprove -Pdpss.gpr --level=2

With the default timeout, one overflow check is unproved. The final check can be
proved by increasing the timeout. I was able to prove all checks with:

      gnatprove -Pdpss.gpr --level=2 --timeout=120
