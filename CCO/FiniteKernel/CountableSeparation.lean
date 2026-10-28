import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.Data.Set.Countable
import Mathlib.Order.Directed

/-!
# Countable linear-functional separation by explicit successive extension

Begin with zero on `R`, adjoin the distinguished vector with value one, then
enumerate the actual ambient module. At each step a vector already in the
domain changes nothing; a new independent vector is assigned zero. The
directed union of this NATURAL-NUMBER sequence has the whole ambient domain.

`LinearPMap.supSpanSingleton` is the elementary one-vector sum/decomposition
construction; `sSup` glues the displayed directed sequence. No Zorn lemma,
arbitrary basis extension or black-box separation theorem is invoked.
-/

universe u v
namespace CCO.FiniteKernel

variable (K : Type u) [Field K] (D : Type v) [AddCommGroup D] [Module K D]

private noncomputable def extendByZero (f : D →ₗ.[K] K) (x : D) : D →ₗ.[K] K := by
  classical
  exact if hx : x ∈ f.domain then f else f.supSpanSingleton x 0 hx

private theorem le_extendByZero (f : D →ₗ.[K] K) (x : D) :
    f ≤ extendByZero K D f x := by
  classical
  unfold extendByZero
  split_ifs with hx
  · exact le_rfl
  · change f ≤ f.sup _ _
    exact LinearPMap.left_le_sup _ _ _

private theorem mem_extendByZero (f : D →ₗ.[K] K) (x : D) :
    x ∈ (extendByZero K D f x).domain := by
  classical
  unfold extendByZero
  split_ifs with hx
  · exact hx
  · change x ∈ f.domain ⊔ Submodule.span K {x}
    exact Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton x))

private noncomputable def extensionSequence (initial : D →ₗ.[K] K) (enum : ℕ → D) :
    ℕ → (D →ₗ.[K] K)
  | 0 => initial
  | n+1 => extendByZero K D (extensionSequence initial enum n) (enum n)

private theorem extensionSequence_monotone (initial : D →ₗ.[K] K) (enum : ℕ → D) :
    Monotone (extensionSequence K D initial enum) := by
  apply monotone_nat_of_le_succ
  intro n
  exact le_extendByZero K D _ _

/-- Extend ANY partial linear form on a countable actual module by the
displayed one-vector-at-a-time algorithm. All old values are retained.
-/
theorem extend_countable_partial_form [Countable D] (initial : D →ₗ.[K] K) :
    ∃ f : D →ₗ[K] K, ∀ x : initial.domain, f x.val = initial x := by
  classical
  obtain ⟨enum,henum⟩ := exists_surjective_nat D
  let seq := extensionSequence K D initial enum
  have hmono : Monotone seq := extensionSequence_monotone K D initial enum
  have hdir : DirectedOn (· ≤ ·) (Set.range seq) := by
    rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩
    exact ⟨seq (max i j), ⟨_,rfl⟩, hmono (le_max_left _ _), hmono (le_max_right _ _)⟩
  let union := LinearPMap.sSup (Set.range seq) hdir
  have hle (n : ℕ) : seq n ≤ union := LinearPMap.le_sSup hdir ⟨n,rfl⟩
  have hdom (x : D) : x ∈ union.domain := by
    obtain ⟨n,rfl⟩ := henum x
    exact (hle (n+1)).1 (mem_extendByZero K D (seq n) (enum n))
  let full : D →ₗ[K] K := {
    toFun := fun x => union ⟨x,hdom x⟩
    map_add' := fun x y => union.toFun.map_add ⟨x,hdom x⟩ ⟨y,hdom y⟩
    map_smul' := fun c x => union.toFun.map_smul c ⟨x,hdom x⟩
  }
  refine ⟨full, ?_⟩
  intro x
  exact ((hle 0).2 (x := x) (y := ⟨x.val,hdom x.val⟩) rfl).symm

/-- C11: every vector outside `R` is separated by an ACTUAL linear form on
the entire countable ambient module, using no compactness or Zorn provider.
-/
theorem exists_countable_separating_form [Countable D]
    (R : Submodule K D) (ell : D) (hell : ell ∉ R) :
    ∃ f : D →ₗ[K] K, (∀ x ∈ R, f x = 0) ∧ f ell = 1 := by
  classical
  let zeroR : D →ₗ.[K] K := ⟨R,0⟩
  let initial := zeroR.supSpanSingleton ell 1 hell
  have hzero : zeroR ≤ initial := by
    change zeroR ≤ zeroR.sup _ _
    exact LinearPMap.left_le_sup _ _ _
  obtain ⟨f,hf⟩ := extend_countable_partial_form K D initial
  refine ⟨f, ?_, ?_⟩
  · intro x hx
    have hm : x ∈ initial.domain := hzero.1 hx
    exact (hf ⟨x,hm⟩).trans ((hzero.2 (x := ⟨x,hx⟩) (y := ⟨x,hm⟩) rfl).symm)
  · have hm : ell ∈ initial.domain :=
      Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton ell))
    exact (hf ⟨ell,hm⟩).trans (LinearPMap.supSpanSingleton_apply_self zeroR 1 hell)

end CCO.FiniteKernel
