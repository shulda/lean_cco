import CCO.APCharacter.Towers.CurrentSource
import CCO.APCharacter.ParitySource

/-! The actual parity and maximal original gate construction is instantiated
on ANY current source state. A residual interval yields a true nonidentity
character source, not a hypothetical stage or a parity predicate callback. -/
universe u v w t
namespace CCO.APCharacter.Towers.CurrentSource
open RigidGroupoid.Geometry
variable (A : CurrentSource.{u,v,w,t})

theorem phase_of_obstruction (h : A.Obstruction) :
    ∃ (i : A.Sorts) (K : Kernel A.source i),
      Nonempty (SourcePhase A.source A.homogeneous
        (exactCalculus_of_homogeneous_CCO A.source A.homogeneous A.cco) K) := by
  obtain ⟨i,E,F,a,hEF,hfin⟩ := h
  letI := hfin
  obtain ⟨Y,U,hYU,hTwo,hUF,hUE,K,hK⟩ := finite_interval_character
    A.source A.homogeneous A.cco E F hEF a
  exact ⟨i,K,hK⟩

end CCO.APCharacter.Towers.CurrentSource
