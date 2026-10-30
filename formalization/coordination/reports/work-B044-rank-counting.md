# B044 C49–C52 — actual unary palettes, orbitals and base-three rank

Author: `/root`. Source remains `490c3f36d85db5a0b3ced0598e6c431825254ec5`.
Four modules, 357 Lean lines, under `CCO.APCharacter.Rank`; no accepted API,
source, contract, shared import, toolchain, manifest or provider change.

`Source` constructs an actual unary refinement of an arbitrary old
`AtomicSource S`: named child sorts are `(i,b)`, their carriers are literal
subtypes `{x : X i // tag i x = b}`, and each child palette is exactly the
subtype of old diversity colours occurring on that ordered child pair.
All child sorts are explicitly nonempty. The forgetful map is injective,
the optional diagonal remains real equality, converse and actual realization
are proved. There are no new binary names or assumed atom-map injectivity.

`Orbitals.same_old_colour_iff_orbit` derives genuine ordered pair orbit
recognition from homogeneity of the WHOLE expanded source. It handles every
fixed ordered child pair, including the same-child specialization. Every
actual remaining child colour is proved to be a complete diversity orbital.
Homogeneity of separate child reducts is not substituted. If the acting group
is the full automorphism group these are literally its orbitals; a homogeneous
colour-preserving subgroup has the same orbits by the proved equivalence.

`Source.child_card_lt` and `child_card_le_pred` use a genuinely missing old
colour and the constructed occurring-colour subtype to obtain the strict
cardinality drop. `inactive_card` proves that a single-label inactive parent
retains its entire old palette, using the old source's actual realization
field. These are palette statements; interpreting their cardinalities as
orbital counts uses the separate whole-source homogeneity lemmas above.

`Potential` proves the exact displayed ACR subtraction expression and strict
decrease with base THREE, for any nonempty finite active family. Each active
parent contributes at most `2 * 3^(k-1) < 3^k`; inactive terms are unchanged.
This is internal numerical support, not the principal source instance.

`Consumer.actual_palette_rank_drop` instantiates that support on the ACTUAL
old/child source palettes, summing over all actual child sorts. Active fibres
have cardinality two and lose a designated old colour; inactive fibres have
cardinality one and their unchanged palette equality is proved. Positivity
of each old active rank follows from the actual designated atom.
`homogeneous_character_rank_drop` bundles the full old/new orbital recognition
and actual ACR inequalities under whole-source homogeneity, with no AP, SAP,
CCO, exactness or external theorem premise. The owning source construction
must still supply its actual unary labels, both nonempty children, missing
phase-one colours and whole expanded homogeneity when applying this theorem.
This helper does not claim that remaining B044 construction is discharged.

Verification: exact Lean4.34.1/Lake5 and unchanged manifest. Narrow final
`lake --rehash build +CCO.APCharacter.Rank.Consumer` passed 979 jobs; all four
modules are actual compiled consumers. No root import edit, broad local suite,
axiom audit or reviewer build/test contribution. Root publication/CI and the
owner's final source union remain separate gates. Local log:
`runtime/round19-rank-consumer.log` outside the Git-backed project.
