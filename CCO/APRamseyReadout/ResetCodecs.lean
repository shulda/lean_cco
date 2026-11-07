import CCO.FullCode.FiniteHidden
import CCO.FullCode.RamseyAge
import CCO.ResetOrder.Normalization
import CCO.ResetOrder.SortRestriction
import Lean.Elab.Tactic.Omega

/-! Faithful changes of record language, with literally the same carriers
and point maps. Every partial unary domain and both relation arities are
retained. This file has no clone, CCO, SAP or normal-form parameters. -/

universe u v w
namespace CCO.APRamseyReadout
noncomputable section
open CCO.FullCode
variable (L : Language.{u})

inductive ResetFunc : ℕ → Type u
  | unary (F : L.Func) : ResetFunc 1

inductive ResetRel : ℕ → Type u
  | unary (U : L.Unary) : ResetRel 1
  | binary (R : L.Binary) : ResetRel 2

abbrev resetLanguage : CCO.ResetOrder.Generic.Language L.Sorts where
  Func := ResetFunc L
  Rel := ResetRel L
  input F := match F with | .unary F => fun _ => L.input F
  output F := match F with | .unary F => L.output F
  argument R := match R with
    | .unary U => fun _ => L.unarySort U
    | .binary R => fun i => if i.val = 0 then L.leftSort R else L.rightSort R

private theorem finOne_eta {V : Type v} (xs : Fin 1 → V) : (fun _ => xs 0) = xs := by
  funext i
  exact congrArg xs (Fin.eq_zero i).symm

private theorem finTwo_eta {V : Type v} (xs : Fin 2 → V) :
    (fun i : Fin 2 => if i.val = 0 then xs 0 else xs 1) = xs := by
  funext i
  by_cases h : i.val = 0
  · have he : i = 0 := Fin.ext h
    subst i; rfl
  · have he : i = 1 := Fin.ext (by have hi := i.isLt; omega)
    subst i; rfl

def resetStructure {V : Type v} (C : Structure L V) :
    CCO.ResetOrder.Generic.Structure (resetLanguage L) V where
  sort := C.sort
  func F xs := match F with | .unary F => C.func F (xs 0)
  functional F xs y z hy hz := by
    cases F with | unary F => exact C.functional F (xs 0) y z hy hz
  func_sorted F xs y hy := by
    cases F with | unary F =>
      have hs := C.func_sorted F (xs 0) y hy
      exact ⟨fun i => by simpa only [Fin.eq_zero i] using hs.1,hs.2⟩
  rel R xs := match R with
    | .unary U => C.unary U (xs 0)
    | .binary R => C.binary R (xs 0) (xs 1)
  rel_sorted R xs h i := by
    cases R with
    | unary U => simpa only [Fin.eq_zero i] using C.unary_sorted U (xs 0) h
    | binary R =>
      have hs := C.binary_sorted R (xs 0) (xs 1) h
      by_cases hi : i.val = 0
      · have he : i = 0 := Fin.ext hi
        subst i; exact hs.1
      · have he : i = 1 := Fin.ext (by have hh := i.isLt; omega)
        subst i; exact hs.2

def resetDecode {V : Type v} (C : CCO.ResetOrder.Generic.Structure (resetLanguage L) V) :
    Structure L V where
  sort := C.sort
  func F x := C.func (.unary F) (fun _ => x)
  functional F x := C.functional (.unary F) (fun _ => x)
  func_sorted F x y h := by
    have hs := C.func_sorted (.unary F) (fun _ => x) y h
    exact ⟨hs.1 0,hs.2⟩
  unary U x := C.rel (.unary U) (fun _ => x)
  unary_sorted U x h := C.rel_sorted (.unary U) (fun _ => x) h 0
  binary R x y := C.rel (.binary R) (fun i => if i.val = 0 then x else y)
  binary_sorted R x y h := ⟨C.rel_sorted (.binary R) _ h 0,C.rel_sorted (.binary R) _ h 1⟩

@[simp] theorem resetDecode_resetStructure {V : Type v} (C : Structure L V) :
    resetDecode L (resetStructure L C) = C := rfl

@[simp] theorem resetStructure_resetDecode {V : Type v}
    (C : CCO.ResetOrder.Generic.Structure (resetLanguage L) V) :
    resetStructure L (resetDecode L C) = C := by
  apply CCO.ResetOrder.Generic.Structure.ext
    (C := resetStructure L (resetDecode L C)) (D := C) rfl
  · funext n F xs
    cases F with | unary F => exact congrArg (C.func (.unary F)) (finOne_eta xs)
  · funext n R xs
    cases R with
    | unary U => exact congrArg (C.rel (.unary U)) (finOne_eta xs)
    | binary R => exact congrArg (C.rel (.binary R)) (finTwo_eta xs)

/-- The entire partial fibre is preserved and reflected. -/
def resetEmbedding {V : Type v} {W : Type w} {C : Structure L V} {D : Structure L W}
    (e : Structure.Embedding C D) :
    CCO.ResetOrder.Generic.Structure.Embedding (resetStructure L C) (resetStructure L D) where
  point := e.point
  injective := e.injective
  sort_eq := e.sort_eq
  func_eq F xs := by
    cases F with | unary F =>
      ext y
      constructor
      · exact fun hy => e.reflect_func F (xs 0) y hy
      · rintro ⟨z,hz,rfl⟩; exact e.map_func F (xs 0) z hz
  rel_iff R xs := by
    cases R with
    | unary U => exact e.unary_iff U (xs 0)
    | binary R => exact e.binary_iff R (xs 0) (xs 1)

def resetDecodeEmbedding {V : Type v} {W : Type w}
    {C : CCO.ResetOrder.Generic.Structure (resetLanguage L) V}
    {D : CCO.ResetOrder.Generic.Structure (resetLanguage L) W}
    (e : CCO.ResetOrder.Generic.Structure.Embedding C D) :
    Structure.Embedding (resetDecode L C) (resetDecode L D) where
  point := e.point
  injective := e.injective
  sort_eq := e.sort_eq
  map_func F x y h := e.map_func (.unary F) (fun _ => x) y h
  reflect_func F x y h := e.reflect_func (.unary F) (fun _ => x) y h
  unary_iff U x := e.rel_iff (.unary U) (fun _ => x)
  binary_iff R x y := by
    have hh := e.rel_iff (.binary R) (fun i => if i.val = 0 then x else y)
    change D.rel (.binary R) (fun i => if i.val = 0 then e.point x else e.point y) ↔ _
    have he : (fun i : Fin 2 => if i.val = 0 then e.point x else e.point y) =
        e.point ∘ (fun i => if i.val = 0 then x else y) := by
      funext i; by_cases hi : i.val = 0 <;> simp only [Function.comp_apply,hi,if_true,if_false]
    rw [he]
    exact hh

def resetEmbeddingOfDecode {V : Type v} {W : Type w}
    {C : CCO.ResetOrder.Generic.Structure (resetLanguage L) V}
    {D : CCO.ResetOrder.Generic.Structure (resetLanguage L) W}
    (e : Structure.Embedding (resetDecode L C) (resetDecode L D)) :
    CCO.ResetOrder.Generic.Structure.Embedding C D :=
  (resetEmbedding L e).cast (resetStructure_resetDecode L C) (resetStructure_resetDecode L D)

@[simp] theorem resetEmbeddingOfDecode_point {V : Type v} {W : Type w}
    {C : CCO.ResetOrder.Generic.Structure (resetLanguage L) V}
    {D : CCO.ResetOrder.Generic.Structure (resetLanguage L) W}
    (e : Structure.Embedding (resetDecode L C) (resetDecode L D)) :
    (resetEmbeddingOfDecode L e).point = e.point :=
  CCO.ResetOrder.Generic.Structure.Embedding.point_cast _ _ _

def resetEmbeddingEquiv {V : Type v} {W : Type w}
    (C : CCO.ResetOrder.Generic.Structure (resetLanguage L) V)
    (D : CCO.ResetOrder.Generic.Structure (resetLanguage L) W) :
    CCO.ResetOrder.Generic.Structure.Embedding C D ≃
      Structure.Embedding (resetDecode L C) (resetDecode L D) where
  toFun := resetDecodeEmbedding L
  invFun := resetEmbeddingOfDecode L
  left_inv e := by
    apply CCO.ResetOrder.Generic.Structure.Embedding.ext
    exact resetEmbeddingOfDecode_point L _
  right_inv e := by
    apply Structure.Embedding.ext
    intro x
    exact congrFun (resetEmbeddingOfDecode_point L e) x

theorem resetDecodeEmbedding_comp {V : Type v} {W : Type w} {Z : Type*}
    {A : CCO.ResetOrder.Generic.Structure (resetLanguage L) V}
    {B : CCO.ResetOrder.Generic.Structure (resetLanguage L) W}
    {C : CCO.ResetOrder.Generic.Structure (resetLanguage L) Z}
    (g : B.Embedding C) (f : A.Embedding B) :
    resetDecodeEmbedding L (g.compose f) = (resetDecodeEmbedding L g).comp (resetDecodeEmbedding L f) := by
  apply Structure.Embedding.ext
  intro x; rfl

def resetObject (A : FiniteHidden.{u,v} L) : CCO.ResetOrder.Generic.Object.{u,v} (resetLanguage L) :=
  ⟨A.Carrier,A.finite,resetStructure L A.model⟩

def resetDecodeObject (A : CCO.ResetOrder.Generic.Object.{u,v} (resetLanguage L)) : FiniteHidden.{u,v} L :=
  ⟨A.Carrier,resetDecode L A.data,A.finite⟩

@[simp] theorem resetDecodeObject_resetObject (A : FiniteHidden.{u,v} L) :
    resetDecodeObject L (resetObject L A) = A := by cases A; rfl

@[simp] theorem resetObject_resetDecodeObject (A : CCO.ResetOrder.Generic.Object.{u,v} (resetLanguage L)) :
    resetObject L (resetDecodeObject L A) = A := by
  cases A with | mk V h C =>
    change CCO.ResetOrder.Generic.Object.mk V h (resetStructure L (resetDecode L C)) = _
    rw [resetStructure_resetDecode]

/-- All-induced-embedding heredity; literal-subset heredity alone is not
silently promoted to this stronger interface. -/
def FullHereditary (K : FiniteHidden.{u,v} L → Prop) : Prop :=
  ∀ {A B}, K B → Structure.Embedding A.model B.model → K A

def resetAge (K : FiniteHidden.{u,v} L → Prop) : CCO.ResetOrder.Generic.Age.{u,v} (resetLanguage L) :=
  fun A => K (resetDecodeObject L A)

theorem resetAge_hereditary {K : FiniteHidden.{u,v} L → Prop} (hK : FullHereditary L K) :
    CCO.ResetOrder.Generic.Hereditary (resetLanguage L) (resetAge L K) := by
  intro A B hB e
  exact hK hB (resetDecodeEmbedding L e)

end
end CCO.APRamseyReadout
