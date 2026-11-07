/-
Copyright (c) 2026 Re'em Melamed-Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Re'em Melamed-Katz
-/

/- CCO compatibility port, 6 November 2026.
Adapted from ReemMelamed/algebraic-automata at
0acb244aaa913c32eeeff48e939cb5df469a3f70 for the receiving
Lean 4.34.1 / Mathlib v4.34.1 environment. Original notices retained.
Compatibility modifications are recorded in PROVENANCE.json and PORT_REPORT.md. -/

module

public import AlgebraicAutomata.GreensRelations.Finite

/-!
# Green's Relations Partial Orders

Partial orders on the quotient types `GreenLClass`, `GreenRClass`, `GreenJClass`,
and `GreenDClass`.

## References

* [T. Colcombet, *The Factorization Forest Theorem*][colcombet2008]
-/

@[expose] public section


namespace GreensRelations

variable {S : Type*} [Semigroup S]

namespace GreenLClass

/-- The partial order on `L`-classes.
`[a] ≤ [b]` iff `a` is a left multiple of `b`. -/
instance : PartialOrder (GreenLClass S) where
  le := Quotient.lift₂ IsGreenLeftDvd fun _ _ _ _ ha hb =>
    propext ⟨fun h => ha.right.trans (h.trans hb.left),
            fun h => ha.left.trans (h.trans hb.right)⟩
  le_refl := Quot.ind IsGreenLeftDvd.refl
  le_trans := Quot.ind fun a ↦ Quot.ind fun b ↦ Quot.ind fun c ↦ IsGreenLeftDvd.trans
  le_antisymm := Quot.ind fun a ↦ Quot.ind fun b hab hba ↦
    mk_eq_mk_iff.mpr ⟨hab, hba⟩

end GreenLClass

namespace GreenRClass

/-- The partial order on `R`-classes.
`[a] ≤ [b]` iff `a` is a right multiple of `b`. -/
instance : PartialOrder (GreenRClass S) where
  le := Quotient.lift₂ IsGreenRightDvd fun _ _ _ _ ha hb =>
    propext ⟨fun h => ha.right.trans (h.trans hb.left),
            fun h => ha.left.trans (h.trans hb.right)⟩
  le_refl := Quot.ind IsGreenRightDvd.refl
  le_trans := Quot.ind fun a ↦ Quot.ind fun b ↦ Quot.ind fun c ↦ IsGreenRightDvd.trans
  le_antisymm := Quot.ind fun a ↦ Quot.ind fun b hab hba ↦
    mk_eq_mk_iff.mpr ⟨hab, hba⟩

end GreenRClass

namespace GreenJClass

/-- The partial order on `J`-classes.
`[a] ≤ [b]` iff `a` is a two-sided multiple of `b`. -/
instance : PartialOrder (GreenJClass S) where
  le := Quotient.lift₂ IsGreenJRel fun _ _ _ _ ha hb =>
    propext ⟨fun h => ha.right.trans (h.trans hb.left),
            fun h => ha.left.trans (h.trans hb.right)⟩
  le_refl := Quot.ind IsGreenJRel.refl
  le_trans := Quot.ind fun a ↦ Quot.ind fun b ↦ Quot.ind fun c ↦ IsGreenJRel.trans
  le_antisymm := Quot.ind fun a ↦ Quot.ind fun b hab hba ↦
    mk_eq_mk_iff.mpr ⟨hab, hba⟩

/-- In a finite semigroup, the quotient of Green's `J`-classes is finite. -/
instance [Finite S] : Finite (GreenJClass S) := Quotient.finite (IsGreenJ.setoid S)

end GreenJClass

namespace GreenDClass

/-- In a finite semigroup, equivalence of D and J relations yields an equivalence
between `GreenDClass S` and `GreenJClass S`. -/
noncomputable def equivGreenJClass [Finite S] : GreenDClass S ≃ GreenJClass S where
  toFun := Quotient.map id fun _ _ ↦ isGreenJ_of_isGreenD
  invFun := Quotient.map id fun _ _ ↦ isGreenD_of_isGreenJ
  left_inv := Quot.ind fun _ ↦ rfl
  right_inv := Quot.ind fun _ ↦ rfl

/-- In a finite semigroup, the quotient of Green's `D`-classes is finite. -/
instance [Finite S] : Finite (GreenDClass S) := Quotient.finite (IsGreenD.setoid S)

/-- The partial order on `D`-classes in a finite semigroup. -/
noncomputable instance [Finite S] : PartialOrder (GreenDClass S) :=
  PartialOrder.lift equivGreenJClass equivGreenJClass.injective

end GreenDClass

end GreensRelations
