# B063 named-source quotient compatibility — author handoff

Assigned author: `/root/b053_resume/b063_functional` (actual B063 author, not reviewer).
Production scope: only `CCO/AutomaticEPCore/NamedIsoQuotient.lean`.
Frozen SHA256: `d68092dcb4e0cb7c7835b82b4fd1ef7cedc4f99c4a5f26a7f3e4f1c09655f2ec`.

## Receiving interface

`namedIsoOriginalCodedQuotientIso A base hOne E s I` constructs
`CodedCurrentSourceIso (originalCodedQuotient A base hOne E (namedIsoExactPrefix s I)) (originalCodedQuotient A base hOne E s)`.
Here `s : CertifiedGateTower.ExactPrefix A`, `E : ExactEq A.source base`,
`hOne : forall i, base = i`, and `I : NamedCurrentSourceIso s.current B`.
There is no assumed quotient-source provider, final-core or separation hypothesis.
The exact-prefix transport/product fields are consumed and discharged by the actual prefix.

## Constructed data

- `namedIsoOriginalOccupancyEquiv`: actual quotient of current names by original E support, transported through `namedIsoReduct I` with proved per-fibre surjectivity.
- `namedIsoOriginalSelectedPointEquiv`: actual WHOLE selected quotient point equivalence through canonical global E-class equivalences and literal unary-reduct projection.
- `_globalE` and `_owner`: exact global-class equality and the actual occupancy owner equation.
- `_palette`: both directions of complete equality-inclusive tagged pair-colour equivalence; uses original/current TP saturation, genuine global atomic-block seed congruence and endpoints. No palette provider is assumed.
- `_rootCode`: equality by VALUE for every fixed original E-saturated predicate coordinate, with no renaming of original predicates.

## Verification

Pinned Lean 4.34.1, strict implicit settings, private output only:

```sh
PATH=/workspace/scratch/e67502cd723c/work-runtime/.runtime-tools/lean-4.34.1-linux/bin:$PATH lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false CCO/AutomaticEPCore/NamedIsoQuotient.lean -o /workspace/scratch/d821f7d92465/b063-functional-iso-quotient.olean
```

Exit 0, zero diagnostics. Separate full-source signature/axiom readback compiled using `--root=/workspace/scratch/d821f7d92465`; file `B063NamedIsoQuotientCheck.lean` and log `b063-named-iso-quotient-signatures.log` are alongside this note.
Readback for final iso, full palette and root-code equality reports only `propext`, `Classical.choice`, `Quot.sound`.
`git diff --check -- CCO/AutomaticEPCore/NamedIsoQuotient.lean` clean.

No source gap identified in this scope. Parent owns public root import, consumer/root compilation, durable report/commit and aligned-history receiving/outer induction. No shared build output, other file, branch, commit, push, CI or coordination was mutated by this subtask.
