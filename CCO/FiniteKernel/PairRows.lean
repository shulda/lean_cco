import CCO.FiniteKernel.LinearDual
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Span.Basic

/-! Actual local pair equations, including valid unary-supported annihilator
rows of a nonsubdirect pair. No freely imposed unary rows are introduced.
For an isolated coordinate there are NO pair rows, so R is zero.
-/

universe u v w
namespace CCO.FiniteKernel
noncomputable section
open scoped DirectSum
variable (K : Type u) [Field K] {I : Type v} (V : I → Type w) [DecidableEq I]
variable [∀ i,AddCommGroup (V i)] [∀ i,Module K (V i)]
variable [∀ i,FiniteDimensional K (V i)]

def pairRow (i j : I) (phi : Module.Dual K (V i × V j)) : TestSpace K V :=
  DirectSum.lof K I (fun i => Module.Dual K (V i)) i (phi.comp (LinearMap.inl K (V i) (V j))) +
  DirectSum.lof K I (fun i => Module.Dual K (V i)) j (phi.comp (LinearMap.inr K (V i) (V j)))

@[simp] theorem eval_pairRow (x : ∀ i,V i) (i j : I) (phi : Module.Dual K (V i × V j)) :
    evalTuple K V x (pairRow K V i j phi) = phi (x i,x j) := by
  simp only [pairRow,map_add,evalTuple_lof,LinearMap.comp_apply,LinearMap.inl_apply,LinearMap.inr_apply]
  rw [← map_add]
  simp only [Prod.mk_add_mk,add_zero,zero_add]

def pairRows (L : ∀ i j,Submodule K (V i × V j)) : Submodule K (TestSpace K V) :=
  Submodule.span K {ell | ∃ i j, i ≠ j ∧ ∃ phi : Module.Dual K (V i × V j),
    phi ∈ (L i j).dualAnnihilator ∧ ell = pairRow K V i j phi}

def pairConstraints (L : ∀ i j,Submodule K (V i × V j)) : Submodule K (∀ i,V i) where
  carrier := {x | ∀ i j, i ≠ j → (x i,x j) ∈ L i j}
  zero_mem' i j _ := (L i j).zero_mem
  add_mem' hx hy i j hij := (L i j).add_mem (hx i j hij) (hy i j hij)
  smul_mem' a x hx i j hij := (L i j).smul_mem a (hx i j hij)

theorem perp_pairRows [∀ i,Countable (V i)]
    (L : ∀ i j,Submodule K (V i × V j)) :
    perp K V (pairRows K V L) = pairConstraints K V L := by
  ext x
  constructor
  · intro hx
    intro i j hij
    by_contra hnot
    obtain ⟨phi,hphi,h1⟩ := exists_countable_separating_form K (V i × V j) (L i j) (x i,x j) hnot
    have hgen : pairRow K V i j phi ∈ pairRows K V L :=
      Submodule.subset_span ⟨i,j,hij,phi,(Submodule.mem_dualAnnihilator _).mpr hphi,rfl⟩
    have hz := (mem_perp K V _ x).mp hx _ hgen
    rw [eval_pairRow,h1] at hz
    exact one_ne_zero hz
  · intro hx
    apply (mem_perp K V _ x).mpr
    intro ell hell
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hell
    · intro d hd
      obtain ⟨i,j,hij,phi,hphi,rfl⟩ := hd
      exact (eval_pairRow K V x i j phi).trans
        ((Submodule.mem_dualAnnihilator _).mp hphi _ (hx i j hij))
    · exact map_zero _
    · intro a b _ _ ha hb
      rw [map_add,ha,hb,add_zero]
    · intro a b _ hb
      rw [map_smul,hb,smul_zero]

theorem ann_pairConstraints [∀ i,Countable (V i)] [Countable (TestSpace K V)]
    (L : ∀ i j,Submodule K (V i × V j)) :
    ann K V (pairConstraints K V L) = pairRows K V L := by
  rw [← perp_pairRows K V L,ann_perp]

theorem pairRows_of_subsingleton [Subsingleton I]
    (L : ∀ i j,Submodule K (V i × V j)) : pairRows K V L = ⊥ := by
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  rintro d ⟨i,j,hij,_⟩
  exact False.elim (hij (Subsingleton.elim i j))

end
end CCO.FiniteKernel
