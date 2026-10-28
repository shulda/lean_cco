import CCO.FiniteKernel.CountableSeparation
import Mathlib.LinearAlgebra.Dual.Defs

/-! Elementary annihilator separation, used for the actual finite marginal
spaces. Its separating form is constructed by the package's explicit
countable extension; no unspecified separation provider is assumed.
-/

universe u v
namespace CCO.FiniteKernel
variable (K : Type u) [Field K] {Y : Type v} [AddCommGroup Y] [Module K Y] [Countable Y]

theorem mem_iff_annihilator_tests (L : Submodule K Y) (y : Y) :
    y ∈ L ↔ ∀ phi : Module.Dual K Y, phi ∈ L.dualAnnihilator → phi y = 0 := by
  constructor
  · intro hy phi hphi
    exact (Submodule.mem_dualAnnihilator phi).mp hphi y hy
  · intro hy
    by_contra hnot
    obtain ⟨phi,hphi,h1⟩ := exists_countable_separating_form K Y L y hnot
    have hz := hy phi ((Submodule.mem_dualAnnihilator phi).mpr hphi)
    rw [h1] at hz
    exact one_ne_zero hz

theorem annihilator_injective :
    Function.Injective (fun L : Submodule K Y => L.dualAnnihilator) := by
  intro L M h
  change L.dualAnnihilator = M.dualAnnihilator at h
  ext y
  rw [mem_iff_annihilator_tests K L y,mem_iff_annihilator_tests K M y,h]

end CCO.FiniteKernel
