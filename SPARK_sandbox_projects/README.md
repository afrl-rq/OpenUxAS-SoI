"Sandbox" Projects for OpenUxAS written in SPARK
================================================================================

This directory contains projects that are related to, but not central to,
OpenUxAS that have been developed in SPARK Ada 2014.

You can get SPARK Ada from AdaCore at: https://www.adacore.com/download You will
want to get both GNAT GPL Ada as well as SPARK Discovery. Note that SPARK
Discovery ships with a reduced set of theorem provers, so you may not be able to
fully replicate the success described here. You can manually install and add
theorem provers to SPARK Discovery, if needed.

# Projects #

There are three projects provided:

1. `DPSS` - a straightforward implementation of the `UAV_Pkg` from
   `AADL_sandbox_projects/DPSS-3` in SPARK Ada.

2. DPSS_position_input - a revised implementation of the `UAV_Pkg` in SPARK Ada
   in which `position` is an input to the component.

3. DPSS_refined_types - a further revision of the `UAV_Pkg` in SPARK Ada in
   which types have been restricted to defined ranges and with predicates.

Each of these projects contains its own `README` that provides additional
explanation.
