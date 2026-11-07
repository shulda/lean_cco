# B063 receiving endpoint transfer — author handoff

Actual author: `/root/b053_resume/b063_functional` (B063 author, not reviewer).
Only assigned production file: `CCO/AutomaticEPCore/NamedIsoEndTransfer.lean`.
Frozen SHA256: `3a0c90759d4ce269a7f978b704ea2c75da75ebe4650d6e56b7846c7531cb68bb`.

## Terminal receiving API

`namedIso_terminal_iff (I : NamedCurrentSourceIso A B) : A.Terminal iff B.Terminal`.
Proof constructs `namedIsoColourOrderIso I i` on the ENTIRE `ColourEq` lattice at every actual sort i, using only whole-source point/palette data. It does not restrict tested equivalences to exact ones. `namedIsoRelativeClassEquiv I i E F a` preserves the actual quotient class sets for every such pair E,F; `namedIso_relative_index` records their exact Nat.card equality. Consequently finite proper intervals, including nonexact/Top intervals, transfer in both directions. No SAP, infinity or terminal provider is assumed to prove the equivalence.

## Literal fixed-code finite tables

`codedPredicateSupport X R s t` means actual points x,y in those precise named sorts satisfy `R (X.code <s,x> <t,y>)`.
`codedPredicateTable X R` is the entire actual binary table; its finiteness is proved from the current finite unary palette.
`codedPredicateSupport_iso_iff I R s t` transfers exactly to image names `I.sorts s,I.sorts t`.
`codedPredicateSupport_target_iff I R s t` reads back actual prescribed target names to their precise inverse image names.
`codedPredicateTable_iso` is equality of tables by exact inverse image under the real sort equivalence, not equality of cardinalities.
`codedValueSupport_iso_iff` keeps any literal value c fixed.
`codedCoordinateSupport_iso_iff` keeps the SAME predicate coordinate a in code `Index -> Prop`, hence applies to the original E-saturated code family without any atom/predicate renaming.
`codedIsoFibre_code` records actual pointwise value equality through the displayed fibre equivalences.

## Direct receiving bridge

`codedExactPrefix_support_target_iff rootCode next I R s t`:

`codedPredicateSupport target R s t iff prefixSupport next.reduct (fun p q => R (rootCode p q)) (I.sorts.symm s) (I.sorts.symm t)`.

Here I is the actual `CodedCurrentSourceIso (codedExactPrefix rootCode next) target`. There is no colour-completeness/provider assumption. The literal original binary relation selected by R is read back on exactly the target endpoint names; both directions use real point witnesses. The forward-image form is `codedExactPrefix_support_iso_iff`.

## Verification

Pinned Lean 4.34.1, strict implicit options, output private:

```sh
PATH=/workspace/scratch/e67502cd723c/work-runtime/.runtime-tools/lean-4.34.1-linux/bin:$PATH lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false CCO/AutomaticEPCore/NamedIsoEndTransfer.lean -o /workspace/scratch/d821f7d92465/b063-functional-end-transfer.olean
```

Exit 0 with zero diagnostics after replacing two proof-local letI binders with let.
Full-source signature/axiom check `B063NamedIsoEndTransferCheck.lean` compiled using `--root=/workspace/scratch/d821f7d92465`; exact log `b063-named-iso-end-transfer-signatures.log` alongside this note. Terminal equivalence, finite table equality, direct target readback and coordinate-preservation axioms are only propext/Classical.choice/Quot.sound. `git diff --check` clean.

No gap in this assigned scope. Parent owns public root imports, all affected consumer/root compilation, durable commits/report and induction assembly. Previous files remain frozen; no shared build output, other production file, branch, commit, push, CI or coordination was mutated. Await separate allocation before any quotient-atom readback file.
