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

/-- The source-facing selected form retains the ORIGINAL parity layer and
the concrete chosen maximal gate through the SAME successor identification.
Every original even pair has equal bits and every original odd pair has
opposite bits; the latter includes the literal positive odd-word relation. -/
theorem selected_safe_exact_split (A : Terminal.CurrentSource.{u,v,w,t})
    (h : A.Obstruction) :
    ∃ B : Terminal.CurrentSource.{u,v,w,t}, ∃ s : Terminal.SelectedStep A B,
      Strong.ActualPhaseSufficiency s.phase A.base.cco
        (SingleStep.identification A.base s.phase) ∧
      (∀ x y : A.base.Point s.sort,
        ParityHasse.Original.evenColourEq A.base.source A.base.homogeneous s.atom x y →
        Terminal.Readout.marking A.base s.phase ⟨s.sort,y⟩ =
          Terminal.Readout.marking A.base s.phase ⟨s.sort,x⟩) ∧
      (∀ x y : A.base.Point s.sort,
        ParityHasse.Relative.odd
          (ParityHasse.Original.evenColourEq A.base.source A.base.homogeneous s.atom).val
          (ParityHasse.Original.connectivityColourEq A.base.source A.base.homogeneous s.atom).val
          x y →
        Terminal.Readout.marking A.base s.phase ⟨s.sort,y⟩ =
          Terminal.Readout.marking A.base s.phase ⟨s.sort,x⟩ + 1) ∧
      (∀ x y : A.base.Point s.sort, ParityHasse.Original.OddWalk
        (A.base.source.atomRel s.atom) x y →
        Terminal.Readout.marking A.base s.phase ⟨s.sort,y⟩ =
          Terminal.Readout.marking A.base s.phase ⟨s.sort,x⟩ + 1) := by
  obtain ⟨B,⟨s⟩⟩ := Terminal.selected_safe_exact_split A h
  exact ⟨B,s,Strong.actual_phase_sufficiency s.phase A.base.cco
    (SingleStep.identification A.base s.phase) A.sap,
    s.original_even,s.original_odd,s.original_odd_walk⟩

end
end CCO.PairSafeSplit
