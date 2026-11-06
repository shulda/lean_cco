import CCO.ExactEPGeometry.OriginalActualNextAtomicSaturation
import CCO.ExactEPGeometry.OriginalSelectedGlobalAtomicBlock
import CCO.ExactEPGeometry.OriginalPhaseSelectedPointEquiv

/-!
# B062 C103: the actual discarded selected quotient has the same FULL palette

The true selected point bijection preserves and reflects equality of every
complete tagged atomic pair colour. Its owner map is the actual occupancy
equivalence, and the binary calculation uses the NEW actual block theorem.
Both seeds and endpoints may move to different canonical selected parents;
their literal global E-classes control these changes. Logical equality is
included. No quotient SAP, group section, or additional provider is used.
-/

universe u v w t
namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.SourceAge
open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

variable (A B : CurrentSource.{u,v,w,t})
variable (P : UnaryReduct A.source B.source)
variable (transport : ExactTraceTransport A.source B.source P)
variable (tp : ExactTraceProduct A.source B.source P)
variable (hOne : ∀ i j : A.Sorts, i = j)
variable {r : B.Sorts} (Kroot : Kernel B.source r)
variable (phase : SourcePhase B.source B.homogeneous
  (exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco) Kroot)
variable (E : ExactEq A.source (P.parent r))
variable (hNot : ¬ E ≤ PrefixExactLargestLift.largest
  A B P transport tp r (current_kernel_exact_eq B Kroot))

include tp hNot

/-- The actual selected-point bijection identifies the FULL original-E
blocks of genuine NEW and OLD selected pair colours, not just a nominal
old orbital table pulled back to points. -/
theorem originalDiscardedSelectedAtomicBlock_iff
    (q s q' s' : Sigma (originalExactSelectedQuotientCurrentSource
      A (SingleStep.successor B phase) (P.compose (SingleStep.projection B phase))
      (ExactTraceTransport.compose P (SingleStep.projection B phase) transport
        (canonical_step_exact_transport B phase)) (P.parent r)
      (fun i => hOne (P.parent r) i) E).Point) :
    let base := P.parent r
    let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
    let N := SingleStep.successor B phase
    let R := SingleStep.projection B phase
    let hN := ExactTraceTransport.compose P R transport (canonical_step_exact_transport B phase)
    let f := originalPhaseSelectedPointEquiv A B P transport Kroot phase base hBase E
    let repN := originalSelectedTaggedRepresentative A N (P.compose R) hN base hBase E
    let repB := originalSelectedTaggedRepresentative A B P transport base hBase E
    originalCurrentExactSaturatedColour A N (P.compose R) base hBase E
      (taggedColour N.source (repN q) (repN s)) (repN q') (repN s') ↔
    originalCurrentExactSaturatedColour A B P base hBase E
      (taggedColour B.source (repB (f q)) (repB (f s))) (repB (f q')) (repB (f s')) := by
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let N := SingleStep.successor B phase
  let R := SingleStep.projection B phase
  let hN := ExactTraceTransport.compose P R transport (canonical_step_exact_transport B phase)
  let f := originalPhaseSelectedPointEquiv A B P transport Kroot phase base hBase E
  let repN := originalSelectedTaggedRepresentative A N (P.compose R) hN base hBase E
  let repB := originalSelectedTaggedRepresentative A B P transport base hBase E
  let T := currentOriginalExactSetoid A B P base hBase E
  have hGlobal (p : Sigma (originalExactSelectedQuotientCurrentSource
      A N (P.compose R) hN base hBase E).Point) :
      T.r (repB (f p)) (R.project (repN p)) :=
    originalPhaseSelectedPointEquiv_globalE A B P transport Kroot phase base hBase E p
  have hNext := originalDiscardedActualNextAtomicSaturation_iff
    A B P transport tp hOne Kroot phase E hNot
      (repN q).2 (repN s).2 (repN q') (repN s')
  have hSeed := originalCurrentExactAtomicBlock_seed_congr
    A B P base hBase E (R.project (repN q)) (R.project (repN s))
      (repB (f q)) (repB (f s)) (R.project (repN q')) (R.project (repN s'))
      (T.symm (hGlobal q)) (T.symm (hGlobal s))
  have hEndpoints := setoidSaturation_congr T
    (fun x y => taggedColour B.source x y = taggedColour B.source (repB (f q)) (repB (f s)))
    (T.symm (hGlobal q')) (T.symm (hGlobal s'))
  exact hNext.trans (hSeed.trans hEndpoints)

/-- Discarding a character step preserves and reflects the ENTIRE actual
selected quotient atomic palette through its true point bijection and
actual occupancy-name equivalence. In particular it preserves equality. -/
theorem originalDiscardedSelectedTaggedColour_iff
    (q s q' s' : Sigma (originalExactSelectedQuotientCurrentSource
      A (SingleStep.successor B phase) (P.compose (SingleStep.projection B phase))
      (ExactTraceTransport.compose P (SingleStep.projection B phase) transport
        (canonical_step_exact_transport B phase)) (P.parent r)
      (fun i => hOne (P.parent r) i) E).Point) :
    let base := P.parent r
    let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
    let N := SingleStep.successor B phase
    let R := SingleStep.projection B phase
    let hN := ExactTraceTransport.compose P R transport (canonical_step_exact_transport B phase)
    let QN := originalExactSelectedQuotientCurrentSource A N (P.compose R) hN base hBase E
    let QB := originalExactSelectedQuotientCurrentSource A B P transport base hBase E
    let f := originalPhaseSelectedPointEquiv A B P transport Kroot phase base hBase E
    taggedColour QN.source q' s' = taggedColour QN.source q s ↔
      taggedColour QB.source (f q') (f s') = taggedColour QB.source (f q) (f s) := by
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let N := SingleStep.successor B phase
  let R := SingleStep.projection B phase
  let hN := ExactTraceTransport.compose P R transport (canonical_step_exact_transport B phase)
  let f := originalPhaseSelectedPointEquiv A B P transport Kroot phase base hBase E
  let e := originalDiscardedOccupancySortClassEquiv A B P transport tp hOne Kroot phase E hNot
  have hOwner (p : Sigma (originalExactSelectedQuotientCurrentSource
      A N (P.compose R) hN base hBase E).Point) : (f p).1 = e p.1 :=
    originalDiscardedSelectedPointEquiv_owner A B P transport tp hOne Kroot phase E hNot p
  have hLeft : q'.1 = q.1 ↔ (f q').1 = (f q).1 := by
    rw [hOwner,hOwner]
    exact e.injective.eq_iff.symm
  have hRight : s'.1 = s.1 ↔ (f s').1 = (f s).1 := by
    rw [hOwner,hOwner]
    exact e.injective.eq_iff.symm
  have hNew := originalExactSelectedTaggedColour_iff_globalBlock
    A N (P.compose R) hN base hBase E q s q' s'
  have hOld := originalExactSelectedTaggedColour_iff_globalBlock
    A B P transport base hBase E (f q) (f s) (f q') (f s')
  have hBlocks := originalDiscardedSelectedAtomicBlock_iff
    A B P transport tp hOne Kroot phase E hNot q s q' s'
  exact hNew.trans ((and_congr hLeft (and_congr hRight hBlocks)).trans hOld.symm)

end
end CCO.ExactEPGeometry
