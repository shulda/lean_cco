# B063 C09–C13 actual author checkpoint

Actual implementation author: `/root/b053_resume/b063_functional`.
Owned production file: `CCO/AutomaticEPCore/FunctionalOriginal.lean`.
This is implementation verification, not nonauthor review or batch completion.

Frozen source/contract/notes and actual AtomicSource/HomogeneousSource APIs were read.
The fixed-sort original-source layer does not assume AP, SAP, CCO, terminality,
exactness, a tower, Ramsey/EP/core or an infinite original source. Parent will
instantiate the generic original presenting group with actual FullAut.

C09: `originalFunctionalGroup G M` is the actual subgroup of ALL real
permutations commuting with G. Its group closure is proved directly.
C10: `original_functional_eval_injective`, `_eq_one_of_fixed`, `_no_fixed`,
`_colour_iff` and `_graph_atom` derive real freeness and the full original
orbital graph biconditional (including the equality convention separately).
C11: `_involutive` and `_square_one` use actual symmetric diversity atoms.
C12: `_inv_eq`, `_mul_comm`, `originalFunctionalCommGroup` and
`_finite` prove a finite abelian exponent-two group. Finiteness injects
all graph codes into Option of the actual finite atomic palette.
C13: `_atom_bipartite` and `_bipartite_atom` produce the actual whole
original atomGraph bipartition. A classical auxiliary well ordering merely
chooses the sides of each two-point component; it is no marked language
predicate and no source/infinite hypothesis.

The parent may use all names under `CCO.AutomaticEPCore`. Every theorem
explicitly takes actual S/H, with fixed original sort inferred. No I01–I08
source conclusion occurs in this proof dependency branch. The existing
OrbitalBipartite module is imported solely for its canonical `atomGraph`
definition, not any CCO/sparse/exactness theorem.

Pinned Lean4.34.1 direct compile with autoImplicit=false and
relaxedAutoImplicit=false passes without diagnostics. Separate scratch
signature/axiom readback and a compiled type/proof dependency traversal pass:
45 transitive CCO constants; no ExactEPGeometry, SimultaneousQuotients,
CloneSAP, FULL ColourEq-lattice or RawExact provider constant. The target
Finite/bipartite exports use only propext/Classical.choice/Quot.sound.
Log: `/workspace/scratch/d821f7d92465/b063-functional-signature-firewall.log`.

No shared root/build output, root imports, report, commit, push, PR or live
coordination record was changed. Parent owns root compilation/publication.

Final source SHA256: `c318ffdf5e134732853e9a416d12f771767206052c9e803ed916e05a58ef30ca`.
