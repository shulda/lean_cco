import CCO.PairSafeSplit.Terminal.Readout
import CCO.PairSafeSplit.SAP.Source

/-! B047 C43/C47: genuine progress at EVERY CURRENT SAP source.
The marked SAP proof is instantiated on the exact already constructed
B044 source, before applying any new-source STRONG calculus. -/

universe u v w t
namespace CCO.PairSafeSplit.Terminal.CurrentSource
open APCharacter APCharacter.SourceAge RigidGroupoid.Geometry
noncomputable section
variable (A : CurrentSource.{u,v,w,t})
variable {i : A.base.Sorts} {K : Kernel A.base.source i}
variable (P : SourcePhase A.base.source A.base.homogeneous
  (exactCalculus_of_homogeneous_CCO A.base.source A.base.homogeneous A.base.cco) K)

/-- The SAME actual old-reduct identification is used for source, rank,
forgetful functor and genuine SAP; no independently supplied next source. -/
def successor : CurrentSource.{u,v,w,t} where
  base := SingleStep.successor A.base P
  sap := SAP.unary_source_sap P A.base.cco (SingleStep.identification A.base P) A.sap

def actualStep : ActualStep A (successor A P) where
  base := SingleStep.actualStep A.base P

theorem actual_potential_drop : (successor A P).potential < A.potential :=
  (actualStep A P).potential_lt

/-- An actual current finite-relative interval constructs its own parity,
original maximal gate and detecting character, then a genuine safe source. -/
theorem actual_progress (h : A.Obstruction) :
    ∃ B : CurrentSource.{u,v,w,t}, Next A B := by
  obtain ⟨i,K,⟨P⟩⟩ := A.base.phase_of_obstruction h
  exact ⟨successor A P,⟨actualStep A P⟩⟩

end
end CCO.PairSafeSplit.Terminal.CurrentSource
