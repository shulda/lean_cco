# B009 C08/C12: original support square localisation

Source pin `490c3f36d85db5a0b3ced0598e6c431825254ec5`. Actual source:
`sections/real_hull/01_relative_separator_and_folding.tex`, collapse (3), and
`sections/real_hull/02_global_finite_fibre_fixer.tex`, spoke-square localisation.
Actual author `/root/b009_fibres/class_intervals`, reused after completing the
independent class branch. Mathematical source checkpoint
`4384ab4387d8de6b1c754ba9f90a9b7ccf0b5c64`.

`CCO/RealHull/Geometry/Localisation.lean` exports:

- `squareMeet S B`: literal finite intersection of the OLD diversity squares.
- `prod_choose_right`: an actual represented RAW middle-colour witness,
  retaining the possibility of logical equality.
- `blocker_square_avoidance S H cco R B hcover hp hfix a ha`: C08 square
  avoidance. The proof uses only the blocker condition, so it proves the
  stronger statement for ANY blocker family, including the source's minimal
  family. Its hypotheses are original homogeneous source/CCO, original globally
  composition-closed support, the displayed fixed spoke and actual square
  memberships. No SAP, exactness or globalisation is used.
- `spoke_square_localisation S H cco R P hP hfix c hc hcover`: C12 final
  `square c ⊆ R` and simultaneously `p c = {p}` for every displayed spoke.
  It chooses a minimum-cardinality blocker among subsets of `{c} ∪ P`. The
  blocker necessarily contains `c`; removing any retained spoke yields an
  outside-R witness in `square c`, contradicting the stronger C08 avoidance.
  This also handles the two-row case directly. The final product conclusion
  invokes the already proved original self-side collapse, as in the source.

The RAW factorisation considers its actual optional intermediate colour.
Logical `none`, diversity `d=p`, and diversity `d∈R` are separate explicit
branches. In the remaining branch, the full blocker separator and actual
rectangle criterion force `p~_R d`, contradicting fixedness. The original
optional composition is used throughout; no associative diversity algebra or
synthetic identity is substituted.

Validation: pinned local Lean/Lake target
`lake build CCO.RealHull.Geometry.Localisation` passes 1000 jobs. All current
localisation obligations are proved; no standing provider remains. Only
targeted Finset.Card and Nat.Find imports were added. Parent owns the single
final B009 whole build, complete source guard, official audit and nonauthor
review. No root/public queue changes were made by this helper.
