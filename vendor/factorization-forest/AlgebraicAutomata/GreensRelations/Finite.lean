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

public import AlgebraicAutomata.GreensRelations.Green
public import AlgebraicAutomata.ForMathlib.Algebra.Group.Opposite

/-!
# Finite Semigroup Theorems for Green's Relations

Structural theorems for Green's relations on finite semigroups, including `D` = `J`.

## References

* [T. Colcombet, *The Factorization Forest Theorem*][colcombet2008]
-/

@[expose] public section


namespace GreensRelations

open MulOpposite

variable {S : Type*} [Semigroup S]

section GreenDAndJ

/-- If `a` and `b` are `J`-related in a finite semigroup, they are also `D`-related. -/
theorem isGreenD_of_isGreenJ [Finite S] {a b : S} (h : IsGreenJ a b) : IsGreenD a b :=
  let ⟨c, hac, hcb⟩ := IsGreenJRel.iff_exists_left_right.mp h.left
  ⟨c,
    MulSeq.isGreenL_of_isGreenLeftDvd_of_isGreenJRel hac
      ((IsGreenJRel.of_isGreenRightDvd hcb).trans h.right),
    MulSeq.isGreenR_of_isGreenRightDvd_of_isGreenJRel hcb
      (h.right.trans (IsGreenJRel.of_isGreenLeftDvd hac))⟩

/-- If `a` and `b` are `D`-related, they satisfy the basic `J`-relation step. -/
theorem isGreenJRel_of_isGreenD {a b : S} : IsGreenD a b → IsGreenJRel a b
  | ⟨z, hL, hR⟩ => IsGreenJRel.iff_exists_left_right.mpr ⟨z, hL.left, hR.left⟩

/-- If `a` and `b` are `D`-related, they are also `J`-related. -/
theorem isGreenJ_of_isGreenD {a b : S} (h : IsGreenD a b) : IsGreenJ a b :=
  ⟨isGreenJRel_of_isGreenD h, isGreenJRel_of_isGreenD h.symm⟩

/-- In a finite semigroup, Green's `D` relation and Green's `J` relation are equal. -/
theorem isGreenD_eq_isGreenJ_of_finite [Finite S] : (IsGreenD : S → S → Prop) = IsGreenJ :=
  funext₂ fun _ _ => propext ⟨isGreenJ_of_isGreenD, isGreenD_of_isGreenJ⟩

/-- If `b` and `a * b` are `D`-related in a finite semigroup, they are `L`-related.
The suffix `sl` stands for semigroup left multiplication. -/
theorem isGreenL_sl_of_isGreenD_sl [Finite S] {a b : S} (h : IsGreenD b (a * b)) :
    IsGreenL b (a * b) := by
  constructor
  · rcases h with ⟨z', hL_bz', hR_z'ab⟩
    obtain ⟨z, hR_bz, hL_zab⟩ := isGreenL_commutes_isGreenR hL_bz' hR_z'ab
    obtain ⟨c, rfl⟩ : ∃ c, z = c * b := hL_zab.left.elim (fun rfl ↦ ⟨a, rfl⟩)
      (fun ⟨w, hw⟩ ↦ ⟨w * a, by rw [hw, mul_assoc]⟩)
    exact hR_bz.left.elim (fun h_eq ↦ IsGreenLeftDvd.trans (.inl h_eq) hL_zab.left)
      (fun ⟨d, hd⟩ ↦ (IsGreenL.trans (MulSeq.greenL_of_eq_mul_mul hd) hL_zab).left)
  · exact Or.inr ⟨a, rfl⟩

/-- Alias for `isGreenL_sl_of_isGreenD_sl`. -/
abbrev isGreenL_of_isGreenD_mul_left := @isGreenL_sl_of_isGreenD_sl

/-- If `a` and `a * b` are `D`-related in a finite semigroup, they are `R`-related.
The suffix `sr` stands for semigroup right multiplication. -/
theorem isGreenR_sr_of_isGreenD_sr [Finite S] {a b : S} (h : IsGreenD a (a * b)) :
    IsGreenR a (a * b) :=
  isGreenR_iff_isGreenL_op.mpr
    (isGreenL_sl_of_isGreenD_sl (IsGreenD.isGreenD_iff_isGreenD_op.mp h))

/-- Alias for `isGreenR_sr_of_isGreenD_sr`. -/
abbrev isGreenR_of_isGreenD_mul_right := @isGreenR_sr_of_isGreenD_sr

/-- Structural properties when `a`, `b`, and `a * b` all belong to the same `D`-class. -/
theorem mul_mem_isGreenD_eqvClass_properties
    [Finite S] {D : Set S} (hD_exists : ∃ x, D = IsGreenD.eqvClass x)
    (a b : S) (ha : a ∈ D) (hb : b ∈ D) (hab : a * b ∈ D) :
    (IsGreenR a (a * b) ∧ IsGreenL b (a * b)) ∧
    (∃ e ∈ D, IsIdempotentElem e ∧ IsGreenL a e ∧ IsGreenR b e) := by
  rcases hD_exists with ⟨x₀, rfl⟩
  have hR := isGreenR_sr_of_isGreenD_sr (ha.trans hab.symm)
  have hL := isGreenL_sl_of_isGreenD_sl (hb.trans hab.symm)
  constructor
  · exact ⟨hR, hL⟩
  · rcases hR.left with ha_eq | ⟨u, hu⟩
    · rcases hL.left with hb_eq | ⟨v, hv⟩
      · have hab_eq : a = b := ha_eq.trans hb_eq.symm
        have he_idem : IsIdempotentElem a := hab_eq.symm ▸ ha_eq.symm
        exact ⟨a, ha, he_idem, IsGreenL.refl a, hab_eq ▸ IsGreenR.refl a⟩
      · have h_b_eq_va : b = v * a := ha_eq ▸ hv
        have he_idem : IsIdempotentElem b := show b * b = b by
          nth_rw 1 [h_b_eq_va]
          rw [mul_assoc, ← hv]
        exact ⟨b, hb, he_idem, ⟨Or.inr ⟨a, ha_eq⟩, Or.inr ⟨v, h_b_eq_va⟩⟩, IsGreenR.refl b⟩
    · rcases hL.left with hb_eq | ⟨v, hv⟩
      · have h_a_eq_bu : a = b * u := hb_eq ▸ hu
        have he_idem : IsIdempotentElem a := show a * a = a by
          nth_rw 2 [h_a_eq_bu]
          rw [← mul_assoc, ← hb_eq, ← h_a_eq_bu]
        exact ⟨a, ha, he_idem, IsGreenL.refl a, ⟨Or.inr ⟨b, hb_eq⟩, Or.inr ⟨u, h_a_eq_bu⟩⟩⟩
      · have h_va_eq_bu : v * a = b * u := by rw [hu, ← mul_assoc, ← hv]
        have hLae : IsGreenL a (v * a) := ⟨Or.inr ⟨a, by grind only⟩, Or.inr ⟨v, rfl⟩⟩
        exact ⟨v * a, IsGreenD.trans ⟨a, IsGreenL.symm hLae, IsGreenR.refl a⟩ ha,
          show v * a * (v * a) = v * a by grind only,
          hLae, ⟨Or.inr ⟨b, by grind only⟩, Or.inr ⟨u, h_va_eq_bu⟩⟩⟩

/-- A `D`-class is regular if and only if there exist
two elements in it whose product is also in the `D`-class. -/
theorem isRegularDClass_iff_exists_mul_mem
    [Finite S] (D : Set S) (hD : ∃ x, D = IsGreenD.eqvClass x) :
    IsRegularDClass D ↔ ∃ a ∈ D, ∃ b ∈ D, a * b ∈ D :=
  ⟨fun hReg ↦
    let ⟨e, heD, he_idem⟩ := (isRegularDClass_iff_exists_idempotent D hD).mp hReg
    ⟨e, heD, e, heD, he_idem.eq.symm ▸ heD⟩,
   fun ⟨a, ha, b, hb, hab⟩ ↦
     let ⟨_, e, heD, he_idem, _⟩ := mul_mem_isGreenD_eqvClass_properties hD a b ha hb hab
     (isRegularDClass_iff_exists_idempotent D hD).mpr ⟨e, heD, he_idem⟩⟩

end GreenDAndJ

section SubgroupsInHClasses

/-- A predicate stating that a set `H : Set S` forms a group under
    the semigroup multiplication restricted to `H`. -/
def IsGroup (H : Set S) : Prop :=
  (∀ x y, x ∈ H → y ∈ H → x * y ∈ H) ∧
  ∃ e ∈ H, IsIdempotentElem e ∧
    (∀ x ∈ H, e * x = x ∧ x * e = x) ∧
    (∀ x ∈ H, ∃ y ∈ H, y * x = e ∧ x * y = e)

/-- Constructive group structure on a set satisfying `IsGroup`. -/
@[instance_reducible]
noncomputable def IsGroup.group {H : Set S} (h : IsGroup H) : Group H where
  mul x y := ⟨x.1 * y.1, h.1 x.1 y.1 x.2 y.2⟩
  mul_assoc x y z := Subtype.ext (mul_assoc x.1 y.1 z.1)
  one := ⟨Classical.choose h.2, (Classical.choose_spec h.2).1⟩
  one_mul x := Subtype.ext ((Classical.choose_spec h.2).2.2.1 x.1 x.2).1
  mul_one x := Subtype.ext ((Classical.choose_spec h.2).2.2.1 x.1 x.2).2
  inv x := ⟨Classical.choose ((Classical.choose_spec h.2).2.2.2 x.1 x.2),
    (Classical.choose_spec ((Classical.choose_spec h.2).2.2.2 x.1 x.2)).1⟩
  inv_mul_cancel x := Subtype.ext
    (Classical.choose_spec ((Classical.choose_spec h.2).2.2.2 x.1 x.2)).2.1

/-- Product of two elements in an `H`-class containing an idempotent remains in the `H`-class. -/
lemma mul_mem_isGreenH_eqvClass_of_idempotent {a : S} {e : S} (he : e ∈ IsGreenH.eqvClass a)
    (he_idem : IsIdempotentElem e) {u v : S} (hu : u ∈ IsGreenH.eqvClass a)
    (hv : v ∈ IsGreenH.eqvClass a) : u * v ∈ IsGreenH.eqvClass a :=
  ⟨IsGreenL.trans (by
     simpa [MulSeq.mul_eq_self_of_isGreenH_idempotent (hv.trans he.symm) he_idem]
       using IsGreenL.mul_right v (hu.trans he.symm).1) hv.1,
   IsGreenR.trans (by
     simpa [MulSeq.mul_eq_self_of_isGreenH_idempotent (hu.trans he.symm) he_idem]
       using IsGreenR.mul_left u (hv.trans he.symm).2) hu.2⟩

/-- An `H`-class either contains no idempotents and is not closed under multiplication,
    or contains an idempotent and is closed under multiplication. -/
theorem isGreenH_eqvClass_disjoint_or_exists_idempotent
    [Finite S] (H : Set S) (hH : ∃ a, H = IsGreenH.eqvClass a) :
    (∀ x y, x ∈ H → y ∈ H → x * y ∉ H) ∨
    (∃ e ∈ H, IsIdempotentElem e ∧ ∀ x y, x ∈ H → y ∈ H → x * y ∈ H) := by
  obtain ⟨a, rfl⟩ := hH
  by_cases h : ∀ x y, x ∈ IsGreenH.eqvClass a → y ∈ IsGreenH.eqvClass a →
    x * y ∉ IsGreenH.eqvClass a
  · exact Or.inl h
  · right
    push Not at h
    obtain ⟨x₀, y₀, hx₀, hy₀, hxy₀⟩ := h
    obtain ⟨_, e, _, he_idem, hLx₀e, hRy₀e⟩ :=
      mul_mem_isGreenD_eqvClass_properties ⟨a, rfl⟩ x₀ y₀
        ⟨a, hx₀.1, IsGreenR.refl _⟩ ⟨a, hy₀.1, IsGreenR.refl _⟩ ⟨a, hxy₀.1, IsGreenR.refl _⟩
    have heH : e ∈ IsGreenH.eqvClass a :=
      ⟨hLx₀e.symm.trans hx₀.1, hRy₀e.symm.trans hy₀.2⟩
    exact ⟨e, heH, he_idem, fun u v huH hvH ↦
      mul_mem_isGreenH_eqvClass_of_idempotent heH he_idem huH hvH⟩

/-- An `H`-class containing an idempotent forms a group. -/
theorem isGreenH_eqvClass_isGroup_of_idempotent
    [Finite S] {H : Set S} (hH : ∃ a, H = IsGreenH.eqvClass a)
    {e : S} (heH : e ∈ H) (he_idem : IsIdempotentElem e) :
    IsGroup H := by
  obtain ⟨a, rfl⟩ := hH
  have h_closed : ∀ x y, x ∈ IsGreenH.eqvClass a → y ∈ IsGreenH.eqvClass a →
      x * y ∈ IsGreenH.eqvClass a :=
    fun u v hu hv ↦ mul_mem_isGreenH_eqvClass_of_idempotent heH he_idem hu hv
  have h_inj : ∀ x : IsGreenH.eqvClass a, Function.Injective (fun u : IsGreenH.eqvClass a ↦
    (⟨u.1 * x.1, h_closed u.1 x.1 u.2 x.2⟩ : IsGreenH.eqvClass a)) :=
      fun x u v h ↦ Subtype.ext <| by
    have h1 : u.1 * x.1 = v.1 * x.1 := Subtype.ext_iff.mp h
    rcases (x.2.trans heH.symm).right.right with rfl | ⟨k, hk⟩
    · exact (MulSeq.mul_eq_self_of_isGreenH_idempotent (u.2.trans heH.symm) he_idem).1.symm.trans <|
        h1.trans (MulSeq.mul_eq_self_of_isGreenH_idempotent (v.2.trans heH.symm) he_idem).1
    · have h2 : u.1 * x.1 * k = v.1 * x.1 * k := by rw [h1]
      simp only [mul_assoc, ← hk] at h2
      exact (MulSeq.mul_eq_self_of_isGreenH_idempotent (u.2.trans heH.symm) he_idem).1.symm.trans <|
        h2.trans (MulSeq.mul_eq_self_of_isGreenH_idempotent (v.2.trans heH.symm) he_idem).1
  have h_id : ∀ x ∈ IsGreenH.eqvClass a, e * x = x ∧ x * e = x := fun x hx ↦ by
    have h := MulSeq.mul_eq_self_of_isGreenH_idempotent (hx.trans heH.symm) he_idem
    exact ⟨h.2, h.1⟩
  have h_inv : ∀ x ∈ IsGreenH.eqvClass a, ∃ y ∈ IsGreenH.eqvClass a, y * x = e ∧ x * y = e := by
    intro x hx
    have h_surj := Finite.injective_iff_bijective.mp (h_inj ⟨x, hx⟩) |>.surjective ⟨e, heH⟩
    obtain ⟨⟨y, hy⟩, hyx⟩ := h_surj
    have hyx_val : y * x = e := Subtype.ext_iff.mp hyx
    have hxy_val : x * y = e := by
      have h_eq : (x * y) * x = e * x := by
        calc (x * y) * x = x * (y * x) := by rw [mul_assoc]
        _ = x * e := by rw [hyx_val]
        _ = x := (h_id x hx).2
        _ = e * x := (h_id x hx).1.symm
      have h_inj_appl : (⟨x * y, h_closed x y hx hy⟩ : IsGreenH.eqvClass a) = ⟨e, heH⟩ :=
        h_inj ⟨x, hx⟩ (Subtype.ext h_eq)
      exact Subtype.ext_iff.mp h_inj_appl
    exact ⟨y, hy, hyx_val, hxy_val⟩
  exact ⟨h_closed, e, heH, he_idem, h_id, h_inv⟩

/-- An `H`-class is either never closed under multiplication or forms a group. -/
theorem isGreenH_eqvClass_dichotomy
    [Finite S] (H : Set S) (hH : ∃ a, H = IsGreenH.eqvClass a) :
    (∀ x y, x ∈ H → y ∈ H → x * y ∉ H) ∨
    ((∀ x y, x ∈ H → y ∈ H → x * y ∈ H) ∧ IsGroup H) :=
  (isGreenH_eqvClass_disjoint_or_exists_idempotent H hH).elim .inl
    (fun ⟨_, heH, he_idem, h_closed⟩ ↦
      .inr ⟨h_closed, isGreenH_eqvClass_isGroup_of_idempotent hH heH he_idem⟩)

/-- Lemma 5.3 (Colcombet): If `a * b = a`, `a * c = a`, and `a` and `b` are `J`-related
    in a finite semigroup, then `b * c = b`. -/
theorem mul_eq_self_of_mul_eq_and_isGreenJ [Finite S] {a b c : S}
    (hab : a * b = a) (hac : a * c = a) (hJ : IsGreenJ a b) :
    b * c = b := by
  have hD : IsGreenD b (a * b) := by
    rw [hab, isGreenD_eq_isGreenJ_of_finite]
    exact hJ.symm
  have hL : IsGreenL b a := by
    simpa [hab] using isGreenL_sl_of_isGreenD_sl hD
  rcases hL.left with rfl | ⟨d, rfl⟩
  · exact hac
  · rw [mul_assoc, hac]

end SubgroupsInHClasses

end GreensRelations
