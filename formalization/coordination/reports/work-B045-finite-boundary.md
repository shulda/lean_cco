# B045 C35 — actual finite clone windows

Actual author `/root`; source pin490c3f36d85db5a0b3ced0598e6c431825254ec5.
Read clone_sap C35/N07 and the selected clone theorem. Public declarations
are under `CCO.CloneSAP.FiniteBoundary` in `FiniteBoundary.lean`.

`source S m hm` is the ACTUAL typed finite-clone source on `X i × Fin m`,
for every m≥2; old atoms remain occurring, c is a new occurring diversity
atom, and logical equality is separate. It uses the literal same clone
colouring on natural index values. `up_injective` is the real inclusion
into the infinite clone source.

`not_ageSAP S m hm i q` proves that this actual source has no SAP for any
chosen actual original point q. The two legs are whole m-element fibres,
and the base is their singleton at index0. In ANY proposed real SAP target,
all images are forced into the common base owner's fibre. The first
induced leg gives an injective map Fin m→Fin m, hence covers that fibre.
The second leg's point1 therefore collides with its image. The asserted
strong overlap would force point1 to be the base point0, contradiction.
Old homogeneity, ordinary AP, CCO and finiteness/countability of Q are
not assumed; finite target objects and every original sort are retained.

`two_clone_square` proves c;c=logical equality for two indices, and
`two_clones_fail_kernel` gives an actual same-owner unequal pair omitted
from that product. `bounded_clone_square` proves c;c=owner equality for
every m≥3 by constructing one of the three indices0/1/2 distinct from
both endpoint indices. This is only the bounded kernel calculation;
`not_ageSAP` still applies. `oneCloneEquiv`, `one_clone_empty` and
`one_clone_old_colour` show that one clone recovers the literal old carrier
and old colours with no c edge, so no universal m=1 SAP failure is claimed.

Pinned Lean4.34.1/bundledLake, unchanged manifest:
`lake build CCO.CloneSAP.FiniteBoundary` passed773jobs incrementally.
No broad test/audit pipeline was repeated locally. Whole-package public
head/main CI, source guards and the standard-three axiom audit remain
required. The actual nonauthor reviewer contributed none of this proof.
