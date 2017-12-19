DPSS_position_input
================================================================================

This SPARK Ada project revises the reference implementation of DPSS found in
`../DPSS`. This implementation modifies the interface of the `UAV_Pkg` to
assume that `position` is an input to the component, rather than a directly
computed element of the component's state.

The component implementation is much simpler, if position is an input and not
a computed element of the component state. Not only is the computation to update
position removed, but all state tracking time and delta time is also removed.

# Philosophy #

Since this project deviates from the AGREE by changing how position is handled,
strict adherence to the AGREE model has been relaxed. The code has been cleaned
up a bit and some variables have been renamed. The two remaining critical
guarantees (`direction_formula` and `goal_formula`) are retained.

# Proof #

All directly stated properties prove automatically at level 2, e.g., using the
following command:

      gnatprove -Pdpss.gpr --level=2

With the default timeout, one overflow check is unproved. The final check can be
proved by increasing the timeout. I was able to prove all checks with:

      gnatprove -Pdpss.gpr --level=2 --timeout=120
