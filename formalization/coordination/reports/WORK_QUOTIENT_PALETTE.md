# Actual quotient finite palette checkpoint

Source pin `490c3f36d85db5a0b3ced0598e6c431825254ec5`; B002 remains
IN_PROGRESS. This is the structural finite-colour part of C28, not an
assertion of quotient homogeneity, AP, triangle fullness or semantic CCO.

`CCO/RawExact/QuotientSourcePalette.lean` constructs
`CCO.RawExact.actualQuotientAtomicSource` for any finite family of actual
equivariant surjections from ONE original sort. The sole substantive
original-source hypothesis is `HomogeneousSource S G`; no SAP, CCO,
countability, exact kernel or quotient provider is used by the palette.

Diversity atoms are the ACTUAL group orbital relations on tagged-distinct
quotient pairs. Finiteness is proved by projecting the finite optional
original palette: every optional original colour has a real representative,
and original pair homogeneity makes its projected pair orbit independent
of that representative. The true tagged diagonal is `none`. Reversal is
literal relation transpose; its involution is proved. Original pair flips
give symmetric loop colours. Every named atom is actually attained.

The exported colour equality criterion is exactly

`P.colour x y = P.colour x' y' ↔ GroupActions.orbital x y x' y'`.

It includes the true diagonal, whose orbit equivalence uses proved original
sort transitivity and actual surjectivity. A separate exported theorem
proves colour invariance under the original group action. These proved
APIs supply the separately implemented quotient homogeneity/AP bridge;
they are not assumptions left for the final source instance.

The generic constructor allows labelled equivariant images, including
duplicate copies. It does NOT claim N10's identity-only-edge exclusion for
such duplicate labels. Actual C26–C28 assembly uses the canonical finite
Setoid family, with its proved identity-sort identification, as required
by the pinned one_original_sort scope. The finite palette construction
does not weaken that later obligation.

Validation: exact Lean4.34.1 and pinned manifest; new module target compiled
in 746 jobs, full root in 988 jobs. After deleting only generated root
CCO output files and rebuilding, importing CCO exposes both the constructor
and the exact colour/orbital API. Official pinned axiom-audit checked all
1,646 root declarations against only propext, Classical.choice and
Quot.sound. Explicit constructor/API axiom prints use the same allowlist.
Every public declaration is imported by CCO.lean. No sorry/admit/new axiom
or mathematical source/toolchain/contract change is introduced.

This local leaf is based on the clean canonical-family checkpoint
0de6950a663efb1c5c45a099a5d654a1ca9e85f1. Full same-batch assembly and
independent review must precede a completed C28 claim. C06 literal cycle
classification and quotient C26/C27 remain explicit separate tasks.
