import CCO.FiniteKernel.Source

/-! Empty tests and small ACTUAL marginal projections. Singleton constraints
are retained, so these statements do not identify intrinsic and binding groups.
-/

universe u v w z t
namespace CCO.FiniteKernel
noncomputable section
variable (K : Type u) [Field K] {I : Type v} (V : I → Type w) [DecidableEq I]
variable [∀ i,AddCommGroup (V i)] [∀ i,Module K (V i)]

theorem restrictedTestSpace_empty : restrictedTestSpace K V ∅ = ⊥ := by
  ext ell
  constructor
  · rintro ⟨phi,rfl⟩
    change extendForm K V ∅ phi = 0
    simp [extendForm]
  · intro hell
    rw [Submodule.mem_bot] at hell
    subst ell
    exact (extendForm K V ∅).range.zero_mem

theorem finiteProjection_empty (N : Submodule K (∀ i,V i)) : finiteProjection K V N ∅ = ⊤ := by
  apply top_unique
  intro z _
  refine ⟨0,N.zero_mem,?_⟩
  funext i
  exact False.elim (Finset.notMem_empty i.val i.property)

theorem marginalRows_le_R (R : Submodule K (TestSpace K V)) (A : Finset I) :
    marginalRows K V R A ≤ R := by
  exact iSup_le fun T => iSup_le fun _ => iSup_le fun _ => inf_le_left

theorem marginalRows_small (R : Submodule K (TestSpace K V)) (A : Finset I) (hc : A.card ≤ 2) :
    marginalRows K V R A = R ⊓ restrictedTestSpace K V A := by
  apply le_antisymm
  · exact le_inf (marginalRows_le_R K V R A) (marginalRows_le K V R A)
  · exact marginalRows_contains K V R (Finset.Subset.refl A) hc

theorem marginalRows_empty (R : Submodule K (TestSpace K V)) : marginalRows K V R ∅ = ⊥ := by
  rw [marginalRows_small K V R ∅ (by simp),restrictedTestSpace_empty,inf_bot_eq]

theorem marginalSpace_empty (N : Submodule K (∀ i,V i)) : marginalSpace K V N ∅ = ⊤ := by
  rw [marginalSpace_small K V N ∅ (by simp),finiteProjection_empty]

end

namespace FinitePartition
variable {X : Type u} {S : BinaryStructure.{u,v,w} X} {I : Type z}
variable (P : FinitePartition S I) (V : I → Type t)
variable [∀ i,AddCommGroup (V i)] [∀ i,Module F2 (V i)]
variable (e : ∀ i,Multiplicative (V i) ≃* P.Intrinsic i)

theorem actual_projection_small [DecidableEq I] (A : Finset I) (hc : A.card ≤ 2) :
    finiteProjection F2 V (P.linearKernel V e) A = marginalSpace F2 V (P.linearKernel V e) A :=
  (marginalSpace_small F2 V (P.linearKernel V e) A hc).symm

end FinitePartition
end CCO.FiniteKernel
