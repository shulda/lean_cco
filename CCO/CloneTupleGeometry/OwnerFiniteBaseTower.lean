import CCO.CloneTupleGeometry.OwnerFiniteBaseAlgebraicity
import CCO.CloneTupleGeometry.OwnerSafeTower

/-! N09 finite iteration: preservation of complete finite-base owner type
finiteness composes along the SAME literal owner reducts of the genuine
phase-indexed safe history. Whole-source homogeneity then reads this as
preservation of actual stabilizer-orbit algebraicity. -/

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 900000
universe u v w
namespace CCO.CloneTupleGeometry
open APCharacter APCharacter.SourceAge APCharacter.Towers
open RigidGroupoid.Geometry TerminalPowers
noncomputable section

namespace UnaryReduct
variable {ι κ ν : Type u} {X : ι → Type v} {Y : κ → Type v} {Z : ν → Type v}
variable {S : AtomicSource.{u,v,w} ι X} {T : AtomicSource.{u,v,w} κ Y}
variable {U : AtomicSource.{u,v,w} ν Z}

/-- No new type becomes algebraic over ANY full finite marked base. The
point and base reducts here are those of this literal unary projection. -/
def OwnerTypesFinitePreserved (P : Towers.UnaryReduct S T) : Prop :=
  ∀ {m : ℕ} (base : Fin m ↪ Sigma Y) {c : κ} (x : Y c),
    (ownerTypeOver T base x).Finite ↔
      (ownerTypeOver S (P.project ∘ base) (P.point c x)).Finite

theorem ownerTypesFinite_identity (S : AtomicSource.{u,v,w} ι X) :
    OwnerTypesFinitePreserved (Towers.UnaryReduct.identity S) := by
  intro m base c x
  rfl

/-- The exact marked-base projection is retained when type preservation
is composed, so no separately chosen base isomorphism enters the proof. -/
theorem ownerTypesFinite_compose
    {P : Towers.UnaryReduct S T} {Q : Towers.UnaryReduct T U}
    (hP : OwnerTypesFinitePreserved P) (hQ : OwnerTypesFinitePreserved Q) :
    OwnerTypesFinitePreserved (P.compose Q) := by
  intro m base c x
  let midBase : Fin m ↪ Sigma Y := base.trans ⟨Q.project,Q.bijective.1⟩
  exact (hQ base x).trans (hP midBase (Q.point c x))

end UnaryReduct

namespace OwnerStage

theorem SafeStep.ownerTypesFinite {B D : OwnerStage.{u,v,w}} (s : SafeStep B D) :
    UnaryReduct.OwnerTypesFinitePreserved s.reduct := by
  cases s with
  | phase P =>
    intro m base c x
    exact owner_child_type_finite_iff B.source B.homogeneous B.ap _ P B.cco
      (B.identification P) base x

/-- C63: every finite-base complete owner type has the SAME algebraicity
status after the entire actual finite safe-split history. -/
theorem history_ownerTypesFinite {B D : OwnerStage.{u,v,w}} (h : History Next B D) :
    UnaryReduct.OwnerTypesFinitePreserved (historyReduct h) := by
  induction h with
  | nil B => exact UnaryReduct.ownerTypesFinite_identity B.source
  | cons hs tail ih =>
    exact UnaryReduct.ownerTypesFinite_compose (Classical.choice hs).ownerTypesFinite ih

/-- Actual pointwise-stabilizer orbit finiteness is preserved over every
finite FULL marked base along the literal history reduct. -/
theorem history_owner_algebraicity_iff {B D : OwnerStage.{u,v,w}} (h : History Next B D)
    {m : ℕ} (base : Fin m ↪ Sigma D.Point) {c : D.Sorts} (x : D.Point c) :
    (ownerOrbitOver (G := FullAut D.source) base x).Finite ↔
      (ownerOrbitOver (G := FullAut B.source)
        ((historyReduct h).project ∘ base) ((historyReduct h).point c x)).Finite := by
  rw [← ownerTypeOver_eq_orbit D.source D.homogeneous base x,
    ← ownerTypeOver_eq_orbit B.source B.homogeneous
      ((historyReduct h).project ∘ base) ((historyReduct h).point c x)]
  exact history_ownerTypesFinite h base x

end OwnerStage
end
end CCO.CloneTupleGeometry
