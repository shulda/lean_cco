import CCO.FullCode.Basic
import Mathlib.Logic.Equiv.Defs

/-! Actual transport of every partial graph and relation, and factorization
through an actual induced embedding.  No choice of a favorable expansion or
closure of an arbitrary old substructure is postulated here. -/

universe u v w z
namespace CCO.FullCode

/-- A named old language inside an expanded language.  All old symbols have
their specified expanded interpretations; new symbols remain unconstrained. -/
structure Reduct (L₀ L₁ : Language.{u}) where
  sortMap : L₁.Sorts → L₀.Sorts
  funcMap : L₀.Func → L₁.Func
  unaryMap : L₀.Unary → L₁.Unary
  binaryMap : L₀.Binary → L₁.Binary
  input_eq : ∀ F, sortMap (L₁.input (funcMap F)) = L₀.input F
  output_eq : ∀ F, sortMap (L₁.output (funcMap F)) = L₀.output F
  unary_eq : ∀ U, sortMap (L₁.unarySort (unaryMap U)) = L₀.unarySort U
  left_eq : ∀ R, sortMap (L₁.leftSort (binaryMap R)) = L₀.leftSort R
  right_eq : ∀ R, sortMap (L₁.rightSort (binaryMap R)) = L₀.rightSort R

namespace Structure
variable {L L₀ L₁ : Language.{u}} {V : Type v} {W : Type w} {Z : Type z}

def reduct (C : Structure L₁ V) (ρ : Reduct L₀ L₁) : Structure L₀ V where
  sort x := ρ.sortMap (C.sort x)
  func F := C.func (ρ.funcMap F)
  functional F := C.functional (ρ.funcMap F)
  func_sorted F x y h := by
    obtain ⟨hx, hy⟩ := C.func_sorted (ρ.funcMap F) x y h
    exact ⟨(congrArg ρ.sortMap hx).trans (ρ.input_eq F),
      (congrArg ρ.sortMap hy).trans (ρ.output_eq F)⟩
  unary U := C.unary (ρ.unaryMap U)
  unary_sorted U x h :=
    (congrArg ρ.sortMap (C.unary_sorted (ρ.unaryMap U) x h)).trans (ρ.unary_eq U)
  binary R := C.binary (ρ.binaryMap R)
  binary_sorted R x y h := by
    obtain ⟨hx, hy⟩ := C.binary_sorted (ρ.binaryMap R) x y h
    exact ⟨(congrArg ρ.sortMap hx).trans (ρ.left_eq R),
      (congrArg ρ.sortMap hy).trans (ρ.right_eq R)⟩

def Embedding.reduct {C : Structure L₁ V} {D : Structure L₁ W}
    (f : Embedding C D) (ρ : Reduct L₀ L₁) :
    Embedding (C.reduct ρ) (D.reduct ρ) where
  point := f.point
  injective := f.injective
  sort_eq x := congrArg ρ.sortMap (f.sort_eq x)
  map_func F := f.map_func (ρ.funcMap F)
  reflect_func F := f.reflect_func (ρ.funcMap F)
  unary_iff U := f.unary_iff (ρ.unaryMap U)
  binary_iff R := f.binary_iff (ρ.binaryMap R)

/-- All domains, values, unary relations and binary comparisons are pulled
back on the specified carrier, without changing a single old point. -/
def comapEquiv (C : Structure L W) (e : V ≃ W) : Structure L V where
  sort x := C.sort (e x)
  func F x := {y | e y ∈ C.func F (e x)}
  functional F x y z hy hz := e.injective (C.functional F (e x) (e y) (e z) hy hz)
  func_sorted F x y hy := C.func_sorted F (e x) (e y) hy
  unary U x := C.unary U (e x)
  unary_sorted U x hx := C.unary_sorted U (e x) hx
  binary R x y := C.binary R (e x) (e y)
  binary_sorted R x y hxy := C.binary_sorted R (e x) (e y) hxy

def comapEquivEmbedding (C : Structure L W) (e : V ≃ W) :
    Embedding (C.comapEquiv e) C where
  point := e
  injective := e.injective
  sort_eq _ := rfl
  map_func _ _ _ h := h
  reflect_func F x y hy := by
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    change e (e.symm y) ∈ C.func F (e x)
    simpa only [e.apply_symm_apply] using hy
  unary_iff _ _ := Iff.rfl
  binary_iff _ _ _ := Iff.rfl

theorem reduct_comapEquiv (C : Structure L₁ W) (ρ : Reduct L₀ L₁) (e : V ≃ W) :
    (C.comapEquiv e).reduct ρ = (C.reduct ρ).comapEquiv e := rfl

theorem reduct_induce (C : Structure L₁ V) (ρ : Reduct L₀ L₁)
    (S : Set V) (hS : C.IsClosed S) :
    (C.induce S hS).reduct ρ =
      (C.reduct ρ).induce S (fun F x hx => hS (ρ.funcMap F) x hx) := rfl

/-- A marked old identification yields an expansion of precisely the old
host.  The hypothesis identifies actual structures over the marked points,
rather than merely their unmarked isomorphism types. -/
theorem same_host_reduct (C : Structure L₀ V) (D : Structure L₁ W)
    (ρ : Reduct L₀ L₁) (e : V ≃ W)
    (marked : (D.reduct ρ).comapEquiv e = C) :
    (D.comapEquiv e).reduct ρ = C := by
  rw [reduct_comapEquiv, marked]

noncomputable def Embedding.factorPoint
    {A : Structure L V} {B : Structure L W} {C : Structure L Z}
    (f : Embedding A C) (j : Embedding B C)
    (image : Set.range f.point ⊆ Set.range j.point) (x : V) : W :=
  Classical.choose (image ⟨x, rfl⟩)

theorem Embedding.factorPoint_spec
    {A : Structure L V} {B : Structure L W} {C : Structure L Z}
    (f : Embedding A C) (j : Embedding B C)
    (image : Set.range f.point ⊆ Set.range j.point) (x : V) :
    j.point (f.factorPoint j image x) = f.point x :=
  Classical.choose_spec (image ⟨x, rfl⟩)

/-- The whole image factors through the actual expanded inclusion.  In
particular this reflects domains of ADDED functions, using `j`'s actual
expanded inducedness, rather than old-language heredity alone. -/
noncomputable def Embedding.factor
    {A : Structure L V} {B : Structure L W} {C : Structure L Z}
    (f : Embedding A C) (j : Embedding B C)
    (image : Set.range f.point ⊆ Set.range j.point) : Embedding A B where
  point := f.factorPoint j image
  injective := by
    intro x y h
    apply f.injective
    exact (f.factorPoint_spec j image x).symm.trans
      ((congrArg j.point h).trans (f.factorPoint_spec j image y))
  sort_eq x := by
    rw [← j.sort_eq, f.factorPoint_spec, f.sort_eq]
  map_func F x y hy := by
    have h := f.map_func F x y hy
    rw [← f.factorPoint_spec j image x] at h
    obtain ⟨z, hz, heq⟩ := j.reflect_func F (f.factorPoint j image x) (f.point y) h
    have hzy : z = f.factorPoint j image y :=
      j.injective (heq.trans (f.factorPoint_spec j image y).symm)
    exact hzy ▸ hz
  reflect_func F x y hy := by
    have h := j.map_func F (f.factorPoint j image x) y hy
    rw [f.factorPoint_spec] at h
    obtain ⟨z, hz, heq⟩ := f.reflect_func F x (j.point y) h
    exact ⟨z, hz, j.injective ((f.factorPoint_spec j image z).trans heq)⟩
  unary_iff U x := by
    rw [← j.unary_iff, f.factorPoint_spec, f.unary_iff]
  binary_iff R x y := by
    rw [← j.binary_iff, f.factorPoint_spec, f.factorPoint_spec, f.binary_iff]

theorem Embedding.factor_comp
    {A : Structure L V} {B : Structure L W} {C : Structure L Z}
    (f : Embedding A C) (j : Embedding B C)
    (image : Set.range f.point ⊆ Set.range j.point) :
    j.comp (f.factor j image) = f := by
  apply Embedding.ext
  exact f.factorPoint_spec j image

end Structure
end CCO.FullCode
