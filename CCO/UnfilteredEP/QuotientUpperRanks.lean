import CCO.UnfilteredEP.QuotientUpperTransport
import CCO.TerminalLattice.QuotientOrbitals
import Mathlib.Order.Cover

/-! The actual full quotient upper-interval isomorphism preserves strict
upper cardinal ranks and every cover, including covers ending at Top. -/

universe u v w t a
namespace CCO.UnfilteredEP
open ParityHasse.Original TransitionClosure QuotientTransport
noncomputable section
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) {i j : ι}
variable (D : ColourEq S i) (E : ColourEq S j)
variable (e : Quotient D.val ≃ Quotient E.val)
variable (equivariant : QuotientEquivariant S H D E e)

/-- Original-source quotient action, with no globally installed instance. -/
def originalQuotientAct (g : G) (q : Quotient D.val) : Quotient D.val :=
  @SMul.smul G (Quotient D.val)
    (TerminalLattice.originalQuotientAction S H D).toSMul g q

theorem originalQuotientAct_eq (g : G) (q : Quotient D.val) :
    originalQuotientAct S H D g q = (originalColourEqAsInvEq S H D).act g q := by
  induction q using Quotient.inductionOn
  rfl

/-- Receive explicit equivariance for the actual originalQuotientAction. -/
theorem quotientEquivariant_of_original
    (commutes : ∀ g q, e (originalQuotientAct S H D g q) =
      originalQuotientAct S H E g (e q)) :
    QuotientEquivariant S H D E e := by
  intro g q
  exact (congrArg e (originalQuotientAct_eq S H D g q).symm).trans
    ((commutes g q).trans (originalQuotientAct_eq S H E g (e q)))

/-- The least full upper equivalence is transported to the least one. -/
theorem quotientUpperIso_bottom :
    quotientUpperIso S H D E e equivariant ⟨D,le_rfl⟩ = ⟨E,le_rfl⟩ := by
  let f := quotientUpperIso S H D E e equivariant
  have lower : (⟨D,le_rfl⟩ : {J : ColourEq S i // D ≤ J}) ≤ f.symm ⟨E,le_rfl⟩ :=
    (f.symm ⟨E,le_rfl⟩).property
  have upper := f.monotone lower
  rw [f.apply_symm_apply] at upper
  exact le_antisymm upper (f ⟨D,le_rfl⟩).property

/-- Strict upper FULL equivalences correspond, not merely a selected MI list. -/
def quotientStrictUpperEquiv :
    {J : ColourEq S i // D < J} ≃ {K : ColourEq S j // E < K} := by
  let f := quotientUpperIso S H D E e equivariant
  have bottom := quotientUpperIso_bottom S H D E e equivariant
  refine {
    toFun := fun J => ⟨(f ⟨J.val,J.property.le⟩).val,?_⟩
    invFun := fun K => ⟨(f.symm ⟨K.val,K.property.le⟩).val,?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · have hlt : (⟨D,le_rfl⟩ : {J : ColourEq S i // D ≤ J}) < ⟨J.val,J.property.le⟩ := J.property
    have moved := f.strictMono hlt
    rw [bottom] at moved
    exact moved
  · have hlt : (⟨E,le_rfl⟩ : {K : ColourEq S j // E ≤ K}) < ⟨K.val,K.property.le⟩ := K.property
    have moved := f.symm.strictMono hlt
    have inverseBottom : f.symm ⟨E,le_rfl⟩ = ⟨D,le_rfl⟩ := by
      rw [← bottom]
      exact f.symm_apply_apply _
    rw [inverseBottom] at moved
    exact moved
  · intro J
    apply Subtype.ext
    change (f.symm (f ⟨J.val,J.property.le⟩)).val = J.val
    exact congrArg (fun p : {K : ColourEq S i // D ≤ K} => p.val)
      (f.symm_apply_apply ⟨J.val,J.property.le⟩)
  · intro K
    apply Subtype.ext
    change (f (f.symm ⟨K.val,K.property.le⟩)).val = K.val
    exact congrArg (fun p : {J : ColourEq S j // E ≤ J} => p.val)
      (f.apply_symm_apply ⟨K.val,K.property.le⟩)

include H e equivariant in
/-- The finite strict-upper rank is invariant under actual quotient transport. -/
theorem quotientStrictUpper_card :
    Nat.card {J : ColourEq S i // D < J} = Nat.card {K : ColourEq S j // E < K} :=
  Nat.card_congr (quotientStrictUpperEquiv S H D E e equivariant)

private theorem upper_covBy_iff {L : Type a} [PartialOrder L] (d : L)
    (p q : {l : L // d ≤ l}) : p ⋖ q ↔ p.val ⋖ q.val := by
  rw [covBy_iff_lt_and_eq_or_eq,covBy_iff_lt_and_eq_or_eq]
  constructor
  · rintro ⟨lt,gap⟩
    refine ⟨lt,fun z hpz hzq => ?_⟩
    rcases gap ⟨z,p.property.trans hpz⟩ hpz hzq with same | same
    · exact Or.inl (congrArg Subtype.val same)
    · exact Or.inr (congrArg Subtype.val same)
  · rintro ⟨lt,gap⟩
    refine ⟨lt,fun z hpz hzq => ?_⟩
    rcases gap z.val hpz hzq with same | same
    · exact Or.inl (Subtype.ext same)
    · exact Or.inr (Subtype.ext same)

/-- Every FULL invariant cover is preserved in its true upper interval. -/
theorem quotientUpperIso_cover (J K : {J : ColourEq S i // D ≤ J}) :
    (quotientUpperIso S H D E e equivariant J).val ⋖
      (quotientUpperIso S H D E e equivariant K).val ↔ J.val ⋖ K.val :=
  (upper_covBy_iff E _ _).symm.trans
    ((apply_covBy_apply_iff (quotientUpperIso S H D E e equivariant)).trans
      (upper_covBy_iff D J K))

end
end CCO.UnfilteredEP
