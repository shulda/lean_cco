import CCO.ExactEPGeometry.DiscardedQuotientClassEquiv
import CCO.ExactEPGeometry.OriginalDiscardedOccupancy

/-!
# B062 C103: discarded phase has the SAME real E-occupancy-sort quotient

For E not below the actual canonical old full exact gate, the
already proved C73–C76 theorem identifies ORIGINAL E-support on
actual successor child SORT NAMES with its exact inverse image
under parent projection. The actual homogeneous marked successor
has an occupied legal child above EVERY old parent: choose one
real original parent point and its true source marking tag.

Therefore the parent map of named sorts is genuinely surjective,
respects and reflects ALL E-occupancy equivalences, and induces
a bijection between the two TRUE quotient sets of named occupancy
sorts. No nominal retyping, child-bit forgetting without proof,
quotient SAP, hypothetical group section, or quotient source/age
isomorphism is asserted.

This is a concrete discarded C103 support- and index-preservation
ingredient. The whole quotient orbital language and full finite
marked age comparison must still be constructed independently.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.SourceAge
open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- C103: the genuine parent projection identifies REAL original
E-occupancy equivalence classes of successor child sort names with
those of preceding current parents when this SourcePhase is discarded.
Both domain/codomain are actual quotients by the original E-support,
not freely chosen finite sort labels. -/
noncomputable def originalDiscardedOccupancySortClassEquiv
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
      A B P transport tp r (current_kernel_exact_eq B Kroot)) :
    let base := P.parent r
    let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
    let Next := SingleStep.successor B phase
    let PP := P.compose (SingleStep.projection B phase)
    OriginalOccupancy A Next PP base hBase E ≃
      OriginalOccupancy A B P base hBase E := by
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let Next := SingleStep.successor B phase
  let PP := P.compose (SingleStep.projection B phase)
  let S := originalExactOccupancySetoid A Next PP base hBase E
  let T := originalExactOccupancySetoid A B P base hBase E
  let f : Next.Sorts → B.Sorts := fun c => c.1
  have hPull : ∀ c d : Next.Sorts, S c d ↔ T (f c) (f d) := by
    intro c d
    exact original_discarded_successor_occupancy_iff
      A B P transport tp hOne Kroot phase E hNot c d
  have hSurj : Function.Surjective f := by
    intro i
    let I := SingleStep.identification B phase
    let x : B.Point i := Classical.choice (B.source.nonemptySort i)
    refine ⟨⟨i,UnarySource.tag I i x⟩,rfl⟩
  have hClassSurj : ∀ i : B.Sorts, ∃ c : Next.Sorts, T i (f c) := by
    intro i
    obtain ⟨c,hc⟩ := hSurj i
    refine ⟨c,?_⟩
    rw [hc]
  exact quotientClassEquiv_of_classwiseSurjective
    S T f hPull hClassSurj

end
end CCO.ExactEPGeometry
