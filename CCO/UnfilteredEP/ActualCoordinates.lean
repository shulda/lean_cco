import CCO.UnfilteredEP.EquivariantCoordinates
import CCO.APRamseyReadout.ActualSource
import CCO.TypedOrbitFrames.ActualProjectionSystem
import CCO.ParityHasse.Original.OrbitalAlgebra
import CCO.UnaryFreshFrames.Quotient.Named

/-!
# Actual terminal coordinates have unique values in each hidden sort

Every symmetry and no-finite-interval premise of the independent coordinate
lemma is discharged on the FULL original clone source. Actual hidden-sort
transitivity and actual term surjectivity are proved from the constructed
projection maps and the original homogeneous action.
-/

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 900000
universe u v w r
namespace CCO.UnfilteredEP
open CCO CCO.ParityHasse.Original CCO.TypedOrbitFrames
open CCO.UnaryTermsReturn CCO.UnaryFreshFrames
noncomputable section

section Source
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G)

include S H in
/-- Pair homogeneity turns every invariant binary relation into a union
of actual symmetric pair colours, including the real equality type. -/
theorem actual_invariant_relations_symmetric (i : ι) :
    InvariantRelationsSymmetric G (X i) := by
  intro R invariant
  exact colourInvariant_symmetric S (groupInvariant_colourInvariant S H invariant)

include H in
/-- Terminality is checked on the FULL lattice, so an arbitrary invariant
coordinate kernel and any invariant strict coarsening satisfy the generic
no-finite-interval hypothesis. No representedness premise is used. -/
theorem actual_no_finite_interval_above
    (terminal : ∀ (i : ι) (E F : ColourEq S i), E < F →
      ∀ x : X i, Infinite (RelativeClass E.val F.val x))
    {i : ι} {T : Type*} [MulAction G T] (tau : X i → T)
    (equivariant : ∀ (g : G) x, tau (g • x) = g • tau x) :
    NoFiniteIntervalAbove (G := G) (Setoid.ker tau) := by
  let E : ColourEq S i := ⟨Setoid.ker tau,groupInvariant_colourInvariant S H (by
    intro g x y h
    change tau x = tau y at h
    change tau (g • x) = tau (g • y)
    rw [equivariant,equivariant,h])⟩
  intro F invariant strict x
  let F' : ColourEq S i := ⟨F,groupInvariant_colourInvariant S H invariant⟩
  have strict' : E < F' := strict
  let : Infinite (RelativeClass E.val F'.val x) := terminal i E F' strict' x
  have zero : Nat.card (RelativeClasses (Setoid.ker tau) F x) = 0 := by
    change Nat.card (RelativeClass E.val F'.val x) = 0
    exact Nat.card_eq_zero_of_infinite
  rw [zero]
  exact Nat.not_lt_zero 1

variable (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
local notation "M" => originalCompletedStructure S H sap nr2
local notation "L" => originalCompletedLanguage S H sap nr2

/-- Pull back the actual hidden automorphism action along the constructed
original-group homomorphism. This defines the action on a named target
sort; it assumes no quotient-action section. -/
@[instance_reducible] def actualHiddenCarrierAction (s : (L).Sorts) :
    MulAction G ((M).Carrier s) :=
  MulAction.compHom ((M).Carrier s) (originalCompletedMotionHom S H sap nr2)

attribute [local instance] actualHiddenCarrierAction

/-- The actual real carrier embeds as its literal real summand. -/
def actualRealPoint (i : ι) (x : X i) : (M).Carrier ⟨⟨i,.inl ()⟩⟩ :=
  ⟨.inl ⟨i,x⟩,rfl⟩

/-- Actual term maps retain the given named output sort. -/
def actualRealTerm {i : ι} {s : (L).Sorts}
    (term : Term L ⟨⟨i,.inl ()⟩⟩ s) : X i → (M).Carrier s :=
  fun x => (M).typedEval term (actualRealPoint S H sap nr2 i x)

theorem actualRealTerm_equivariant {i : ι} {s : (L).Sorts}
    (term : Term L ⟨⟨i,.inl ()⟩⟩ s) (g : G) (x : X i) :
    actualRealTerm S H sap nr2 term (g • x) = g • actualRealTerm S H sap nr2 term x := by
  apply Subtype.ext
  exact ((M).aut_eval (originalCompletedMotionHom S H sap nr2 g) term (.inl ⟨i,x⟩)).symm

/-- Every actual hidden target sort is transitive under the ORIGINAL
group. Proper quotient targets use the actual onto projection, while the
real case uses original one-point homogeneity. -/
theorem actual_hidden_carrier_transitive (s : (L).Sorts) :
    ∀ x y : (M).Carrier s, ∃ g : G, g • x = y := by
  rcases s with ⟨i,kind⟩
  cases kind with
  | inl tag =>
      cases tag
      intro x y
      obtain ⟨a,ha⟩ := original_completed_real_carrier_exists S H sap nr2 x
      obtain ⟨b,hb⟩ := original_completed_real_carrier_exists S H sap nr2 y
      obtain ⟨g,hg⟩ := S.original_sort_transitive_of_homogeneous H i a b
      refine ⟨g,?_⟩
      apply Subtype.ext
      change originalCompletedNamedAct S H g x.val = y.val
      rw [ha,hb]
      exact congrArg (fun a : X i => (Sum.inl ⟨i,a⟩ : OriginalCompletedNamedCarrier S H)) hg
  | inr D =>
      intro x y
      obtain ⟨p,hp⟩ := original_projection_typedEval_surjective S H sap nr2 D x
      obtain ⟨q,hq⟩ := original_projection_typedEval_surjective S H sap nr2 D y
      obtain ⟨a,ha⟩ := original_completed_real_carrier_exists S H sap nr2 p
      obtain ⟨b,hb⟩ := original_completed_real_carrier_exists S H sap nr2 q
      obtain ⟨g,hg⟩ := S.original_sort_transitive_of_homogeneous H i a b
      refine ⟨g,?_⟩
      have hReal : g • p = q := by
        apply Subtype.ext
        change originalCompletedNamedAct S H g p.val = q.val
        rw [ha,hb]
        exact congrArg (fun a : X i => (Sum.inl ⟨i,a⟩ : OriginalCompletedNamedCarrier S H)) hg
      rw [← hp,← hq]
      apply Subtype.ext
      change (originalCompletedMotionHom S H sap nr2 g) • (M).eval _ p.val = (M).eval _ q.val
      rw [(M).aut_eval]
      exact congrArg ((M).eval _) (congrArg Subtype.val hReal)

/-- A term from a nonempty real sort is onto its SAME named transitive
hidden target. Its image is invariant by actual equivariance. -/
theorem actualRealTerm_surjective {i : ι} {s : (L).Sorts}
    (term : Term L ⟨⟨i,.inl ()⟩⟩ s) :
    Function.Surjective (actualRealTerm S H sap nr2 term) := by
  obtain ⟨a⟩ := S.nonemptySort i
  intro b
  obtain ⟨g,hg⟩ := actual_hidden_carrier_transitive S H sap nr2 s
    (actualRealTerm S H sap nr2 term a) b
  exact ⟨g • a,(actualRealTerm_equivariant S H sap nr2 term g a).trans hg⟩

/-- C21–C23: all real-source terms with the SAME hidden target agree
literally, regardless of their initial selected quotient coordinate.
The invariant interval contradiction is discharged on the FULL lattice. -/
theorem actual_real_terms_eq
    (terminal : ∀ (i : ι) (E F : ColourEq S i), E < F →
      ∀ x : X i, Infinite (RelativeClass E.val F.val x))
    {i : ι} {s : (L).Sorts}
    (left right : Term L ⟨⟨i,.inl ()⟩⟩ s) :
    actualRealTerm S H sap nr2 left = actualRealTerm S H sap nr2 right := by
  exact (equivariant_surjections_eq (actual_invariant_relations_symmetric S H i)
    (actual_hidden_carrier_transitive S H sap nr2 s)
    (actualRealTerm S H sap nr2 right) (actualRealTerm S H sap nr2 left)
    (actualRealTerm_equivariant S H sap nr2 right)
    (actualRealTerm_equivariant S H sap nr2 left)
    (actualRealTerm_surjective S H sap nr2 right)
    (actualRealTerm_surjective S H sap nr2 left)
    (actual_no_finite_interval_above S H terminal _
      (actualRealTerm_equivariant S H sap nr2 right)))

end Source
end
end CCO.UnfilteredEP
