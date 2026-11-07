import CCO.FullCode.Presentations
import CCO.APRamseyReadout.TupleScheme
import CCO.TerminalHiddenHN.NormalForms
import Mathlib.Basic.Finite.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.SetTheory.Cardinal.Finite

/-! B061 C39: the two explicit finite template bounds. Marked partial
term presentations give the support bound; literal tagged coordinate
tuples give the root bound. Neither estimate uses Ramsey, cofinality,
expansion property, or an algebraic-closure identification. -/

universe u v a
namespace CCO.APRamseyReadout
open CCO.FullCode

/-- All coordinate positions and normal forms give one honest uniform
per-root overbound, even when some presentations are undefined or share
their value. The visible and hidden carrier universes are independent. -/
theorem template_card_bound {L : Language.{u}} {V : Type v}
    {C : Structure L V} {S : RootScheme L} {A : Type a} [Finite A]
    (N : NormalForms L) (O : Object C S A) (hN : N.Valid C) :
    Nat.card O.support ≤ Nat.card (Presentation N S) * Nat.card A := by
  classical
  choose root presentation mem using fun x : O.support =>
    (O.mem_support_iff_presentation N hN x.val).mp x.property
  let code : O.support → A × Presentation N S := fun x => ⟨root x,presentation x⟩
  have hcode : Function.Injective code := by
    intro x y hxy
    have hr : root x = root y := congrArg Prod.fst hxy
    have hp : presentation x = presentation y := congrArg Prod.snd hxy
    apply Subtype.ext
    apply (O.root (root y)).presentation_functional N (presentation y)
    · simpa only [hr,hp] using mem x
    · exact mem y
  calc
    Nat.card O.support ≤ Nat.card (A × Presentation N S) :=
      Nat.card_le_card_of_injective code hcode
    _ = Nat.card A * Nat.card (Presentation N S) := Nat.card_prod _ _
    _ = Nat.card (Presentation N S) * Nat.card A := Nat.mul_comm _ _

/-- The finite sum counts every ordered coordinate tuple at every tag.
Compatibility and sort tests can only decrease the number of roots. -/
noncomputable def rootTupleBound {L : Language.{u}} (S : RootScheme L) (n : ℕ) : ℕ := by
  classical
  letI : Fintype S.Tag := Fintype.ofFinite _
  exact ∑ s : S.Tag, n ^ S.arity s

/-- Count literal tagged roots without quotienting them or choosing
realizers. This also covers zero-coordinate tags in the generic scheme. -/
theorem root_card_bound {L : Language.{u}} {V : Type v} [Finite V]
    (C : Structure L V) (S : RootScheme L) :
    Nat.card (Root C S) ≤ rootTupleBound S (Nat.card V) := by
  classical
  letI : Fintype S.Tag := Fintype.ofFinite _
  let code : Root C S → (s : S.Tag) × (Fin (S.arity s) → V) :=
    fun r => ⟨r.tag,r.coordinate⟩
  have hcode : Function.Injective code := by
    intro r s h
    cases r with | mk rt rc rs rv =>
      cases s with | mk st sc ss sv =>
        have ht : rt = st := (Sigma.mk.inj h).1
        cases ht
        have hc : rc = sc := eq_of_heq (Sigma.mk.inj h).2
        cases hc
        rfl
  calc
    Nat.card (Root C S) ≤ Nat.card ((s : S.Tag) × (Fin (S.arity s) → V)) :=
      Nat.card_le_card_of_injective code hcode
    _ = ∑ s : S.Tag, Nat.card (Fin (S.arity s) → V) := Nat.card_sigma
    _ = ∑ s : S.Tag, Nat.card V ^ S.arity s := by
      simp only [Nat.card_fun,Nat.card_fin]
    _ = rootTupleBound S (Nat.card V) := rfl

universe w p z

section Actual
open CCO.CloneTupleGeometry
noncomputable section
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal) (F : Charts.{u,v,w,p} B)

/-- The finite forms are actual functions on EVERY canonical hidden
input; the list is independent of the selected visible chart. -/
abbrev tupleNormalForms : NormalForms (CoordinateLanguage B ht) :=
  CCO.TerminalHiddenHN.binaryNormalForms (cloneSource B) (cloneHomogeneous B)
    (cloneSAP B) (fullCovers B ht)

/-- Actual finite-age membership supplies full partial-domain validity,
including proper orphan inputs, without a caller-supplied normalizer. -/
theorem tupleNormalForms_valid_of_actualAge {V : Type z}
    (C : CCO.UnarySupport.Structure (Sig B ht) V) (hC : ActualAge B ht C) :
    (tupleNormalForms B ht).Valid (CoordinateModel B ht C) :=
  CCO.TerminalHiddenHN.binaryNormalForms_valid_of_actualAge
    (cloneSource B) (cloneHomogeneous B) (cloneSAP B) (fullCovers B ht) C hC

def tuplePresentationBudget : ℕ :=
  Nat.card (Presentation (tupleNormalForms B ht) (tupleScheme B ht F))

/-- Source C39's first bound for the canonical fixed-chart tuples.
All normal-form hypotheses are discharged on the actual host. -/
theorem actual_template_card_bound {V : Type z} {A : Type a} [Finite A]
    (C : CCO.UnarySupport.Structure (Sig B ht) V) (hC : ActualAge B ht C)
    (O : Object (CoordinateModel B ht C) (tupleScheme B ht F) A) :
    Nat.card O.support ≤ tuplePresentationBudget B ht F * Nat.card A :=
  template_card_bound (tupleNormalForms B ht) O
    (tupleNormalForms_valid_of_actualAge B ht C hC)

/-- Source C39's second bound counts every actual tagged tuple using
exactly the fixed chart arities; validity only reduces that number. -/
theorem actual_root_card_bound {V : Type z}
    (C : CCO.UnarySupport.Structure (Sig B ht) V) (hC : ActualAge B ht C) :
    Nat.card (Root (CoordinateModel B ht C) (tupleScheme B ht F)) ≤
      rootTupleBound (tupleScheme B ht F) (Nat.card V) := by
  letI : Finite V := hC.1
  exact root_card_bound (CoordinateModel B ht C) (tupleScheme B ht F)

/-- Every actual selected chart has a coordinate, so an empty hidden
carrier has zero possible tuples; no empty-coordinate root is inserted. -/
theorem tuple_rootTupleBound_zero : rootTupleBound (tupleScheme B ht F) 0 = 0 := by
  classical
  unfold rootTupleBound
  apply Finset.sum_eq_zero
  intro s _
  exact zero_pow (ne_of_gt (tupleScheme_positive B ht F s))

end
end Actual

end CCO.APRamseyReadout
