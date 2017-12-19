DPSS
================================================================================

This SPARK Ada project provides an implementation of DPSS based on Jen's work
in `OpenUxAS/AADL_sandbox_projects/DSS-3`. The implementation realizes the AADL
component `UAV_Pkg` and required files. Specifically included are:

| File                | Purpose                                     |
+---------------------+---------------------------------------------+
| DPSS_Data_Types.ads | SPARK types for the AADL types introduced   |
| DPSS_Constants.ads  | SPARK constants for the AADL constants      |
| UAV_Pkg.ads         | SPARK specification for the UAV_Pkg package |
| UAV_Pkg.adb         | SPARK body for the UAV_Pkg package          |

All of these files are contained in the `src` subdirectory.

# Philosophy #

The overriding goal in this implementation was to stay as close to the AADL
specification as was practical. Jen's formalization of DPSS in AADL is
sufficiently complete that little additional effort was required to build an
implementation. The most significant complications were:

- determining how to represent the previous value of state elements, so as to
  provide an implementation for the Lustre `prev` operator;

- determining how best to represent time, since SPARK has no built-in notion of
  time, unlike AADL; and

- determining how best to handle initialization and inputs that are constant
  after initialization.

These design decisions are documented in the SPARK Ada code using comments. Look
for the `-- NOTE:` comment blocks for more information.

# Organization #

The `UAV_Pkg` package has been organized so that it has two procedures:

1. `initialize_component`, which is intended to be run once, to set up initial
   state for the component; and

2. `run_component`, which is intended to be run repeatedly, and represents the
   state-update procedure for the package

Some AGREE assumptions have been entered as preconditions on
`initialize_component`; other assumptions are encoded directly or placed on
`run_component`.

The three critical guarantees, "Direction Formula", "Goal Formula", and
"Position Formula" are encoded as predicate expression functions and are
asserted as postconditions on the `run_component` procedure. Additional
postconditions on `run_component` and on `initialize_component` ensure that
state updates are consistent.

# Proof #

All directly stated properties prove automatically at level 2, e.g., using the
following command:

      gnatprove -Pdpss.gpr --level=2

There are 11 overflow checks that **do not prove** at any level. There is
currently insufficient information in the preconditions to ensure that overflow
will not occur.
