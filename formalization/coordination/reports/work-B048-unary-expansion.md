# B048 C26 structural canonical naming after unary expansion

Author: `/root/b047_pair_safe_split/infinite_type_fibres`.
Source pin `490c3f36d85db5a0b3ced0598e6c431825254ec5`; B048 public claim STATE388.

The disjoint helper `Canonical/UnaryExpansion.lean` uses the shared actual
`Marked.addBit` signature (`Marked/Signature.lean`, native `db6e8bb`). It does
not introduce a second full-language encoding or a prefix-model callback.

- `oldProfile` and `profileBit` are literal finite profile decoders. Their
  `*_marked` lemmas commute with the actual interpretation of `Marked.table`.
- `markedProfile_ext` proves these decoded data determine the WHOLE new
  profile, rather than merely preserving selected old binary predicates.
- `marked_profile_eq_iff` works for arbitrary finite slot count k, including
  k=0, and different carriers/full tables: expanded profile equality iff the
  complete old profile and every named endpoint bit agree. All original
  repeated-argument and nullary relation reads are therefore retained.
- `marked_unaryProfile_eq_iff` specializes to old unary type plus the one bit;
  `marked_pairProfile_eq_iff` specializes to old pair type plus BOTH endpoint
  bits, in both directions. These are the structural source-name seams used
  by the separate actual prefix pair-age comparison proof.
- `sameSortSymmetric_of_iso` transports old symmetry through an actual FULL
  isomorphism. `sameSortSymmetric_marked` then proves new same-sort symmetry.
  `sameSortSymmetric_decoded` applies directly to any complete new table T
  given the genuine full old-reduct isomorphism `(Marked.oldTable T) ≅ U`.
  No binary-reduct/full-automorphism identification is asserted.
- `irreducible_marked` retains full irreducibility because every old relation
  remains a literal symbol. `marked_expanded_irreducible` discharges the old
  premise using the previously proved actual canonical naming construction.

Native proof commit `cec3d18e7c0a0f1823858e9776dff0647b584530` compiled with:

```
lake build CCO.FullPhaseLift.Canonical.UnaryExpansion
```

The narrow target succeeded (1346 jobs, including incremental replay) with
pinned Lean4.34.1, unchanged manifest and private worktree outputs. Only this
helper and this report are authored here. Root owns the assembled project
build, exact-head CI and transitive axiom audit. Prior canonical freeze
`b3c13ae` and actual marked pairSAP `2a69a67` remain on preserved branches.
No new axiom, sorry, provider premise or unpublished batch dependency.
