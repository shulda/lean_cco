import CCO.PairSafeSplit.StrongSaturation
import CCO.PairSafeSplit.Full.Closure
import CCO.PairSafeSplit.Full.Gates
import CCO.PairSafeSplit.Full.Factorisation
import CCO.PairSafeSplit.Infinity.Definability
import CCO.PairSafeSplit.Infinity.OldWitnesses
import CCO.PairSafeSplit.Terminal.OrbitCriterion
import CCO.PairSafeSplit.Strong.Sufficiency
import CCO.PairSafeSplit.Terminal.Elimination

/-! All B047 proof branches meet at the SAME actual split. The phase is
constructed from the current finite relative interval; its exact canonical
marked source has independently proved SAP before its STRONG readout.
The inherited actual step retains the literal unary reduct and rank drop. -/

universe u v w t
namespace CCO.PairSafeSplit
open APCharacter APCharacter.SourceAge RigidGroupoid.Geometry
noncomputable section

/-- Source `thm:safe-exact-split`, with the independently proved actual
STRONG sufficiency package attached to the exact identified successor.
No phase, new-source SAP, completion, normal-form or progress callback is
provided by the caller. -/
theorem safe_exact_split (A : Terminal.CurrentSource.{u,v,w,t}) (h : A.Obstruction) :
    ∃ (i : A.base.Sorts) (K : Kernel A.base.source i)
      (P : SourcePhase A.base.source A.base.homogeneous
        (exactCalculus_of_homogeneous_CCO A.base.source A.base.homogeneous A.base.cco) K),
      Strong.ActualPhaseSufficiency P A.base.cco (SingleStep.identification A.base P) ∧
      Nonempty (Terminal.CurrentSource.ActualStep A (A.successor P)) ∧
      (A.successor P).potential < A.potential ∧
      (∀ (b : Reached A.base.source K) (x y : A.base.Point b.val),
        (P.atSort b).rel x y →
        Terminal.Readout.marking A.base P ⟨b.val,y⟩ =
          Terminal.Readout.marking A.base P ⟨b.val,x⟩ + 1) := by
  obtain ⟨i,K,P,hs,hd,ho⟩ := Terminal.safe_exact_split A h
  exact ⟨i,K,P,Strong.actual_phase_sufficiency P A.base.cco
    (SingleStep.identification A.base P) A.sap,hs,hd,ho⟩

end
end CCO.PairSafeSplit
