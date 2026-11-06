import CCO.ExactEPGeometry.DiscardedQuotientClassEquiv
import CCO.ExactEPGeometry.OriginalDiscardedOccupancy

/-!
# B062 C103: discarded ACTUAL source split preserves each entire original E-class quotient

For E NOT below the actual original greatest gate of the current
SourcePhase, the genuine C73–C76 classwise theorem shows EVERY
E-class of a current parent sort meets EVERY actually legal child
of that parent. Forgetting the child phase bit is not surjective on
old POINTS, but it is surjective on real original E-CLASSES.

The source's actual global original-E setoids on the tagged old
CurrentSource carrier and its literal SingleStep successor pull back
to the same original E relation on real projected endpoints.
The generic fully proved classwise quotient equivalence therefore
identifies the actual old parent's original E-class carrier with
the selected child carrier's original E-class carrier.

This is a concrete source C103 discarded step ingredient: no
fake point-surjectivity, no quotient SAP, no automorphism section,
no additional equality/diversity colour, and no assumed quotient
successor SOURCE equivalence. The full quotient age and finite
tower induction remain separate source obligations.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.SourceAge
open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- A real discarded maximal-character step changes NO local
original-E quotient class carrier. The source and target classes
are genuine setoid quotients of actual old and child points, both
defined via the SAME original old E on their true projected images.
This remains valid when a child is not pointwise onto its parent. -/
noncomputable def originalDiscardedChildOriginalEclassEquiv
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (hOne : ∀ i j : A.Sorts, i = j)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (phase : SourcePhase B.source B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) Kroot)
    (E : ExactEq A.source (P.parent r))
    (hNot : ¬ E ≤ PrefixExactLargestLift.largest
      A B P transport tp r (current_kernel_exact_eq B Kroot))
    (c : (SingleStep.successor B phase).Sorts) :
    let base := P.parent r
    let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
    let Next := SingleStep.successor B phase
    let PP := P.compose (SingleStep.projection B phase)
    let EOld := currentOriginalExactSetoid A B P base hBase E
    let ENew := currentOriginalExactSetoid A Next PP base hBase E
    let Rold : Setoid (B.Point c.1) :=
      Setoid.comap (fun x => (⟨c.1,x⟩ : Sigma B.Point)) EOld
    let Rnew : Setoid (Next.Point c) :=
      Setoid.comap (fun x => (⟨c,x⟩ : Sigma Next.Point)) ENew
    Quotient Rnew ≃ Quotient Rold := by
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let Next := SingleStep.successor B phase
  let PP := P.compose (SingleStep.projection B phase)
  let EOld := currentOriginalExactSetoid A B P base hBase E
  let ENew := currentOriginalExactSetoid A Next PP base hBase E
  let Rold : Setoid (B.Point c.1) :=
    Setoid.comap (fun x => (⟨c.1,x⟩ : Sigma B.Point)) EOld
  let Rnew : Setoid (Next.Point c) :=
    Setoid.comap (fun x => (⟨c,x⟩ : Sigma Next.Point)) ENew
  let f : Next.Point c → B.Point c.1 := Subtype.val
  have hPull : ∀ x y : Next.Point c,
      Rnew x y ↔ Rold (f x) (f y) := by
    intro x y
    change (originalExactGlobalRelation A base hBase E)
      (PP.project ⟨c,x⟩) (PP.project ⟨c,y⟩) ↔
      (originalExactGlobalRelation A base hBase E)
      (P.project ⟨c.1,x.val⟩) (P.project ⟨c.1,y.val⟩)
    exact Iff.rfl
  have hClassSurj : ∀ y : B.Point c.1, ∃ x : Next.Point c,
      Rold y (f x) := by
    intro y
    let I := SingleStep.identification B phase
    let d : Next.Sorts := ⟨c.1,UnarySource.tag I c.1 y⟩
    let x0 : Next.Point d := ⟨y,rfl⟩
    have hSupport : (originalExactOccupancySetoid
        A B P base hBase E).r d.1 c.1 :=
      (originalExactOccupancySetoid A B P base hBase E).refl c.1
    obtain ⟨x,hXY⟩ := original_discarded_class_hits_every_supported_child
      A B P transport tp hOne Kroot phase E hNot
      d c hSupport x0
    refine ⟨x,?_⟩
    change (originalExactGlobalRelation A base hBase E)
      (P.project ⟨c.1,y⟩) (P.project ⟨c.1,x.val⟩)
    change (originalExactGlobalRelation A base hBase E)
      (PP.project ⟨d,x0⟩) (PP.project ⟨c,x⟩) at hXY
    exact hXY
  exact quotientClassEquiv_of_classwiseSurjective
    Rnew Rold f hPull hClassSurj

end
end CCO.ExactEPGeometry
