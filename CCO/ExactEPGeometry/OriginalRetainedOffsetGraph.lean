import CCO.ExactEPGeometry.OriginalRetainedChildOccupancy
import Mathlib.Tactic.Abel

/-!
# B062 C81: actual retained E-occupancy offset graphs

For one ACTUAL retained SourcePhase, choose a reached parent a as
the representative of its original E-occupancy component. The true
G-identity arrows from every reached member b,c to a have phase
characters gamma_b, gamma_c. The complete C78/C79 source bridge
composition and C81 classwise child occupancy prove:

   E-support(b_epsilon,c_eta) iff
   epsilon + gamma_b = eta + gamma_c.

This is the EXACT two offset graphs of the frozen source theorem
on actual successor sort names. Both sides use the same original
one-sort exact E, same selected gate, and same genuine SourcePhase.
No quotient SAP, independently chosen phase, hidden group section,
unrealized child type or arbitrary mixed RAW reverse descent.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.SourceAge
open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- C81 coherent corrected-bit graph criterion on ALL actually
realized successor children of ANY two active parents in the SAME
original E-component. The anchor is a genuine reached parent,
not an invented canonical quotient orbit. -/
theorem original_retained_children_offset_graph_iff
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
    (hE : E ≤ PrefixExactLargestLift.largest A B P transport tp r
      (current_kernel_exact_eq B Kroot))
    (a b c : Reached B.source Kroot)
    (hba : (originalExactOccupancySetoid
      A B P (P.parent r) (fun i => hOne (P.parent r) i) E).r b.val a.val)
    (hca : (originalExactOccupancySetoid
      A B P (P.parent r) (fun i => hOne (P.parent r) i) E).r c.val a.val)
    (ε : UnarySource.β (SingleStep.identification B phase) b.val)
    (η : UnarySource.β (SingleStep.identification B phase) c.val) :
    letI := Reached.groupoid B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) (A := Kroot)
    (originalExactOccupancySetoid
      A (SingleStep.successor B phase)
      (P.compose (SingleStep.projection B phase))
      (P.parent r) (fun i => hOne (P.parent r) i) E).r
        (⟨b.val,ε⟩ : (SingleStep.successor B phase).Sorts)
        (⟨c.val,η⟩ : (SingleStep.successor B phase).Sorts) ↔
    ε.val + phase.character.value
      (original_retained_identity_arrow
        A B P transport tp hOne Kroot E hE b a hba) =
    η.val + phase.character.value
      (original_retained_identity_arrow
        A B P transport tp hOne Kroot E hE c a hca) := by
  let C := exactCalculus_of_homogeneous_CCO
    B.source B.homogeneous B.cco
  letI := Reached.groupoid B.homogeneous C (A := Kroot)
  let J := originalExactOccupancySetoid
    A B P (P.parent r) (fun i => hOne (P.parent r) i) E
  let hbc : J.r b.val c.val := J.trans hba (J.symm hca)
  let Ibc := original_retained_identity_arrow
    A B P transport tp hOne Kroot E hE b c hbc
  let γb := phase.character.value
    (original_retained_identity_arrow
      A B P transport tp hOne Kroot E hE b a hba)
  let γc := phase.character.value
    (original_retained_identity_arrow
      A B P transport tp hOne Kroot E hE c a hca)
  have hGamma : phase.character.value Ibc = γb + γc :=
    original_retained_gamma_add
      A B P transport tp hOne Kroot phase E hE a b c hba hca
  have hChild := original_retained_children_occupancy_iff
    A B P transport tp hOne Kroot phase E hE b c hbc ε η
  have hDouble (z : ZMod 2) : z + z = 0 := by decide
  constructor
  · intro hOcc
    have hBit : η.val = ε.val + (γb + γc) := by
      have h := hChild.mp hOcc
      rw [hGamma] at h
      exact h
    calc
      ε.val + γb = (ε.val + (γb + γc)) + γc := by
        calc
          ε.val + γb = (ε.val + γb) + (γc + γc) := by
            rw [hDouble]
            simp
          _ = (ε.val + (γb + γc)) + γc := by abel
      _ = η.val + γc := by rw [hBit]
  · intro hOffset
    apply hChild.mpr
    have hBit : η.val = ε.val + (γb + γc) := by
      calc
        η.val = η.val + 0 := (add_zero _).symm
        _ = η.val + (γc + γc) := by rw [hDouble]
        _ = (η.val + γc) + γc := by abel
        _ = (ε.val + γb) + γc := by rw [← hOffset]
        _ = ε.val + (γb + γc) := by abel
    calc
      η.val = ε.val + (γb + γc) := hBit
      _ = ε.val + phase.character.value Ibc := by rw [hGamma]

end
end CCO.ExactEPGeometry
