import CCO.ExactEPGeometry.ActualPhaseMaximalGate
import CCO.ExactEPGeometry.OriginalRetainedActualSelectedPhase
import CCO.ExactEPGeometry.OriginalRetainedReachedOriginalQuotientGate

/-!
# B062 C103: the ACTUAL retained selected phase has a genuine maximal gate

Apply the proved whole-SourcePhase maximality theorem to the precisely
constructed corrected selected SourcePhase. Its actual root kernel is the
same projected full K/E already obtained from every old reached object.
The witness is a genuine diversity orbital in the earlier selected quotient,
with no odd closed walks, an actual relative-index-two parity interval, and
maximality against ALL full RAW-exact complement equivalences.

This discharges the maximal-gate provider on the ACTUAL selected quotient,
without resampling its corrected character or presupposing a quotient safe
step. The existing original G/E largest-lift theorem uses only the earlier
prefix. A separate actual full-age source isomorphism identifies this SAME
phase's canonical successor with the next original-E selected quotient.
-/

universe u v w t
namespace CCO.ExactEPGeometry
open APCharacter APCharacter.Towers RigidGroupoid.Geometry
open CCO.ParityHasse.Original CCO.ParityHasse.Relative
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
variable (hE : E ≤ PrefixExactLargestLift.largest A B P transport tp r
  (current_kernel_exact_eq B Kroot))

include phase in
/-- The SAME actual corrected selected phase is based at the true K/E
maximal parity complement. All pivot/index/maximality data are constructed,
not requested as another quotient-source provider. -/
theorem originalRetainedActualSelectedGate_complete :
    let base := P.parent r
    let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
    let Q := originalExactSelectedQuotientCurrentSource A B P transport base hBase E
    let KQ := originalRetainedSelectedKernel A B P transport tp hOne Kroot E hE
      (Reached.root Kroot)
    ∃ c : Q.source.Atom (Quotient.mk'' r) (Quotient.mk'' r),
      (∀ x : Q.Point (Quotient.mk'' r), ∀ n : Nat,
        Odd n → ¬relPow (Q.source.atomRel c) n x x) ∧
      (∀ x : Q.Point (Quotient.mk'' r),
        relativeIndex (evenColourEq Q.source Q.homogeneous c).val
          (connectivityColourEq Q.source Q.homogeneous c).val x = 2) ∧
      (∀ x y : Q.Point (Quotient.mk'' r),
        (KQ.rel x y ∧ ConnectedWalk (Q.source.atomRel c) x y) ↔
          EvenWalk (Q.source.atomRel c) x y) ∧
      ∃ M : MaximalGate Q.source Q.homogeneous
        (evenColourEq Q.source Q.homogeneous c)
        (connectivityColourEq Q.source Q.homogeneous c),
        M.kernel = (current_kernel_exact_eq Q KQ).val := by
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let Q := originalExactSelectedQuotientCurrentSource A B P transport base hBase E
  let KQ := originalRetainedSelectedKernel A B P transport tp hOne Kroot E hE
    (Reached.root Kroot)
  let φ := originalRetainedActualSelectedPhase A B P transport tp hOne Kroot phase E hE
  obtain ⟨c,hNoOdd,hIndex,M,hK⟩ := actualPhaseRoot_maximalGate Q KQ φ
  refine ⟨c,hNoOdd,hIndex,?_,M,hK⟩
  intro x y
  have hMeet := M.maximal.1.2.2
  rw [hK] at hMeet
  have h := congrArg (fun Z : ColourEq Q.source (Quotient.mk'' r) => Z.val x y) hMeet
  exact Iff.of_eq h

/-- The selected maximal gate is still precisely the OLD supplied kernel
under its genuine surjective selected original-E projection. This is the
literal current trace needed beside the original G/E largest-lift theorem. -/
theorem originalRetainedActualSelectedGate_rootPullback :
    let base := P.parent r
    let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
    let KQ := originalRetainedSelectedKernel A B P transport tp hOne Kroot E hE
      (Reached.root Kroot)
    originalExactSelectedAtParentKernelPullback A B P transport base hBase E KQ = Kroot := by
  let C := exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco
  exact (originalRetainedSelectedKernel_parentPullback A B P transport tp hOne Kroot E hE
    (Reached.root Kroot)).trans (Reached.root_kernel B.homogeneous C (A := Kroot))

end
end CCO.ExactEPGeometry
