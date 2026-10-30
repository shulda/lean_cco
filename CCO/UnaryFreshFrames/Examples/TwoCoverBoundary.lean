import CCO.UnaryFreshFrames.Examples.TwoCoverOriginal
import CCO.UnaryFreshFrames.SAPFresh

namespace CCO.UnaryFreshFrames.Examples.TwoCover
open Structure

/-- Literal named projection terms in the ORIGINAL signature. -/
def tauTerm : Term originalLanguage 0 1 :=
  Term.func (L := originalLanguage) (0 : Fin 4) (Term.id (L := originalLanguage) (0 : Fin 3))

def pTerm : Term originalLanguage 0 2 :=
  Term.func (L := originalLanguage) (2 : Fin 4) (Term.id (L := originalLanguage) (0 : Fin 3))

def ProperKernel {j : originalLanguage.Sorts} (t : Term originalLanguage 0 j) : Prop :=
  ∃ x y, sort x = 0 ∧ sort y = 0 ∧ x ≠ y ∧ originalModel.eval t x = originalModel.eval t y

theorem tau_proper_kernel : ProperKernel tauTerm := by
  refine ⟨real 0 false 0,real 0 false 1,rfl,rfl,?_,rfl⟩
  intro he
  exact Nat.zero_ne_one (congrArg coordinate he)

theorem p_proper_kernel : ProperKernel pTerm := by
  refine ⟨real 0 false 0,real 0 false 1,rfl,rfl,?_,rfl⟩
  intro he
  exact Nat.zero_ne_one (congrArg coordinate he)

/-- All nonreal vertices have ACTUAL named surjective quotient
representations from the real sort, with kernels strictly above identity. -/
theorem every_hidden_named_quotient (u : Point) (hu : sort u ≠ 0) :
    ∃ t : Term originalLanguage 0 (sort u), ProperKernel t ∧
      ∃ x, sort x = 0 ∧ originalModel.eval t x = u := by
  rcases u with ⟨⟨q,d⟩,n⟩ | (⟨q,d⟩ | q)
  · exact False.elim (hu rfl)
  · exact ⟨tauTerm,tau_proper_kernel,real q d 0,rfl,rfl⟩
  · exact ⟨pTerm,p_proper_kernel,real q false 0,rfl,rfl⟩

/-- τ genuinely is unforced for p: two points of ONE actual p-fibre
have distinct τ values, whose entire image cardinality is exactly two. -/
theorem tau_unforced_for_p : ¬ ForcedBy 2 (Term.func (L := language) (0 : Fin 4)
    (Term.id (L := language) (0 : Fin 3))) := by
  intro h
  have he := h (real 0 false 0) (real 0 true 0) rfl rfl rfl
  exact Bool.false_ne_true (congrArg bit he)

/-- A real source-scope counterexample, not a finite reservoir control:
all structural real-base hypotheses hold, but a hidden root has an
algebraic value outside its actual named closure, so hereditary SAP fails. -/
theorem original_not_ageSAP : ¬ originalModel.AgeSAP := by
  intro hsap
  have hinf := originalModel.infiniteClosedOrbits_of_ageSAP
    original_locallyFinite original_homogeneous hsap
  have hi := hinf {rootPoint 0} (Set.finite_singleton _)
    (singleton_root_closed 0) (middle 0 false) (by simp [middle,rootPoint])
  exact hi (original_algebraic_off_closure 0 false).1

/-- Finite language and countable carrier are actual properties of this
model, alongside the proved homogeneity/local-finiteness diagnostics. -/
theorem original_scope : Countable Point ∧ Finite originalLanguage.Sorts ∧
    Finite originalLanguage.Func ∧ Finite originalLanguage.Rel ∧
    originalModel.Homogeneous ∧ originalModel.LocallyFinite :=
  ⟨inferInstance,inferInstance,inferInstance,inferInstance,
    original_homogeneous,original_locallyFinite⟩

end CCO.UnaryFreshFrames.Examples.TwoCover
