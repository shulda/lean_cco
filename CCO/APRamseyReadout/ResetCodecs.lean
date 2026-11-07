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
      · have he : i = 1 := Fin.ext (by change i.val = 1; have hh : i.val < 2 := i.isLt; omega)
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
      funext i; by_cases hi : i.val = 0 <;> simp only [Function.comp_apply,hi,ite_true,ite_false]
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


/-- Unary-reset view used by the accepted closed-sort restriction. -/
abbrev resetUnarySignature : CCO.ResetOrder.Unary.Primitive.Signature.{u} where
  Sorts := L.Sorts
  Func := L.Func
  Rel := L.Unary ⊕ L.Binary
  input := L.input
  output := L.output
  arity R := match R with | .inl _ => 1 | .inr _ => 2
  argument R := match R with
    | .inl U => fun _ => L.unarySort U
    | .inr R => fun i => if i.val = 0 then L.leftSort R else L.rightSort R

def resetUnaryStructure {V : Type v} (C : Structure L V) :
    CCO.ResetOrder.Unary.Primitive.Structure (resetUnarySignature L) V where
  sort := C.sort
  func := C.func
  functional := C.functional
  func_sorted := C.func_sorted
  rel R xs := match R with
    | .inl U => C.unary U (xs 0)
    | .inr R => C.binary R (xs 0) (xs 1)
  rel_sorted R xs h i := by
    cases R with
    | inl U => simpa only [Fin.eq_zero i] using C.unary_sorted U (xs 0) h
    | inr R =>
      have hs := C.binary_sorted R (xs 0) (xs 1) h
      by_cases hi : i.val = 0
      · have he : i = 0 := Fin.ext hi
        subst i; exact hs.1
      · have he : i = 1 := Fin.ext (by change i.val = 1; have hh : i.val < 2 := i.isLt; omega)
        subst i; exact hs.2

def resetUnaryDecode {V : Type v}
    (C : CCO.ResetOrder.Unary.Primitive.Structure (resetUnarySignature L) V) : Structure L V where
  sort := C.sort
  func := C.func
  functional := C.functional
  func_sorted := C.func_sorted
  unary U x := C.rel (.inl U) (fun _ => x)
  unary_sorted U x h := C.rel_sorted (.inl U) (fun _ => x) h 0
  binary R x y := C.rel (.inr R) (fun i => if i.val = 0 then x else y)
  binary_sorted R x y h := ⟨C.rel_sorted (.inr R) _ h 0,C.rel_sorted (.inr R) _ h 1⟩

@[simp] theorem resetUnaryDecode_structure {V : Type v} (C : Structure L V) :
    resetUnaryDecode L (resetUnaryStructure L C) = C := rfl

private theorem resetUnary_ext {V : Type v}
    {C D : CCO.ResetOrder.Unary.Primitive.Structure (resetUnarySignature L) V}
    (hs : C.sort = D.sort) (hf : C.func = D.func) (hr : C.rel = D.rel) : C = D := by
  cases C; cases D; cases hs; cases hf; cases hr; rfl

@[simp] theorem resetUnaryStructure_decode {V : Type v}
    (C : CCO.ResetOrder.Unary.Primitive.Structure (resetUnarySignature L) V) :
    resetUnaryStructure L (resetUnaryDecode L C) = C := by
  apply resetUnary_ext L (C := resetUnaryStructure L (resetUnaryDecode L C)) (D := C) rfl rfl
  funext R xs
  cases R with
  | inl U => exact congrArg (C.rel (.inl U)) (finOne_eta xs)
  | inr R => exact congrArg (C.rel (.inr R)) (finTwo_eta xs)

def resetUnaryEmbedding {V : Type v} {W : Type w} {C : Structure L V} {D : Structure L W}
    (e : Structure.Embedding C D) :
    CCO.ResetOrder.Unary.Hom (resetUnaryStructure L C) (resetUnaryStructure L D) where
  point := e.point
  injective := e.injective
  sort_eq := e.sort_eq
  map_func := e.map_func
  reflect_func := e.reflect_func
  map_rel R xs h := by
    cases R with
    | inl U => exact (e.unary_iff U (xs 0)).mpr h
    | inr R => exact (e.binary_iff R (xs 0) (xs 1)).mpr h
  reflect_rel R xs h := by
    cases R with
    | inl U => exact (e.unary_iff U (xs 0)).mp h
    | inr R => exact (e.binary_iff R (xs 0) (xs 1)).mp h

def resetUnaryDecodeEmbedding {V : Type v} {W : Type w}
    {C : CCO.ResetOrder.Unary.Primitive.Structure (resetUnarySignature L) V}
    {D : CCO.ResetOrder.Unary.Primitive.Structure (resetUnarySignature L) W}
    (e : CCO.ResetOrder.Unary.Hom C D) :
    Structure.Embedding (resetUnaryDecode L C) (resetUnaryDecode L D) where
  point := e.point
  injective := e.injective
  sort_eq := e.sort_eq
  map_func := e.map_func
  reflect_func := e.reflect_func
  unary_iff U x := ⟨e.reflect_rel (.inl U) (fun _ => x),e.map_rel (.inl U) (fun _ => x)⟩
  binary_iff R x y := by
    have hh : D.rel (.inr R) (e.point ∘ (fun i => if i.val = 0 then x else y)) ↔
        C.rel (.inr R) (fun i => if i.val = 0 then x else y) :=
      ⟨e.reflect_rel (.inr R) _,e.map_rel (.inr R) _⟩
    change D.rel (.inr R) (fun i => if i.val = 0 then e.point x else e.point y) ↔ _
    have he : (fun i : Fin 2 => if i.val = 0 then e.point x else e.point y) =
        e.point ∘ (fun i => if i.val = 0 then x else y) := by
      funext i; by_cases hi : i.val = 0 <;> simp only [Function.comp_apply,hi,ite_true,ite_false]
    rw [he]
    exact hh

def resetUnaryEmbeddingOfDecode {V : Type v} {W : Type w}
    {C : CCO.ResetOrder.Unary.Primitive.Structure (resetUnarySignature L) V}
    {D : CCO.ResetOrder.Unary.Primitive.Structure (resetUnarySignature L) W}
    (e : Structure.Embedding (resetUnaryDecode L C) (resetUnaryDecode L D)) :
    CCO.ResetOrder.Unary.Hom C D where
  point := e.point
  injective := e.injective
  sort_eq := e.sort_eq
  map_func := e.map_func
  reflect_func := e.reflect_func
  map_rel R xs h := by
    cases R with
    | inl U =>
      have hh := (e.unary_iff U (xs 0)).mpr (by rw [← finOne_eta xs] at h; exact h)
      change D.rel (.inl U) (fun _ => e.point (xs 0)) at hh
      exact (congrArg (D.rel (.inl U)) (finOne_eta (e.point ∘ xs))) ▸ hh
    | inr R =>
      have hh := (e.binary_iff R (xs 0) (xs 1)).mpr (by rw [← finTwo_eta xs] at h; exact h)
      change D.rel (.inr R) (fun i => if i.val = 0 then e.point (xs 0) else e.point (xs 1)) at hh
      exact (congrArg (D.rel (.inr R)) (finTwo_eta (e.point ∘ xs))) ▸ hh
  reflect_rel R xs h := by
    cases R with
    | inl U =>
      have hh : (resetUnaryDecode L D).unary U (e.point (xs 0)) := by
        change D.rel (.inl U) (fun _ => e.point (xs 0))
        exact (congrArg (D.rel (.inl U)) (finOne_eta (e.point ∘ xs))).symm ▸ h
      have ht := (e.unary_iff U (xs 0)).mp hh
      change C.rel (.inl U) (fun _ => xs 0) at ht
      rw [finOne_eta xs] at ht
      exact ht
    | inr R =>
      have hh : (resetUnaryDecode L D).binary R (e.point (xs 0)) (e.point (xs 1)) := by
        change D.rel (.inr R) (fun i => if i.val = 0 then e.point (xs 0) else e.point (xs 1))
        exact (congrArg (D.rel (.inr R)) (finTwo_eta (e.point ∘ xs))).symm ▸ h
      have ht := (e.binary_iff R (xs 0) (xs 1)).mp hh
      change C.rel (.inr R) (fun i => if i.val = 0 then xs 0 else xs 1) at ht
      rw [finTwo_eta xs] at ht
      exact ht

def resetUnaryEmbeddingEquiv {V : Type v} {W : Type w}
    (C : CCO.ResetOrder.Unary.Primitive.Structure (resetUnarySignature L) V)
    (D : CCO.ResetOrder.Unary.Primitive.Structure (resetUnarySignature L) W) :
    CCO.ResetOrder.Unary.Hom C D ≃ Structure.Embedding (resetUnaryDecode L C) (resetUnaryDecode L D) where
  toFun := resetUnaryDecodeEmbedding L
  invFun := resetUnaryEmbeddingOfDecode L
  left_inv _ := CCO.ResetOrder.Unary.hom_ext (fun _ => rfl)
  right_inv _ := Structure.Embedding.ext (fun _ => rfl)

def resetUnaryObject (A : FiniteHidden.{u,v} L) : CCO.ResetOrder.Unary.Object.{u,v} (resetUnarySignature L) :=
  ⟨A.Carrier,A.finite,resetUnaryStructure L A.model⟩

def resetUnaryDecodeObject (A : CCO.ResetOrder.Unary.Object.{u,v} (resetUnarySignature L)) : FiniteHidden.{u,v} L :=
  ⟨A.Carrier,resetUnaryDecode L A.data,A.finite⟩

@[simp] theorem resetUnaryDecodeObject_object (A : FiniteHidden.{u,v} L) :
    resetUnaryDecodeObject L (resetUnaryObject L A) = A := by cases A; rfl

def resetUnaryAge (K : FiniteHidden.{u,v} L → Prop) : CCO.ResetOrder.Unary.Age.{u,v} (resetUnarySignature L) :=
  fun A => K (resetUnaryDecodeObject L A)

theorem resetUnaryAge_hereditary {K : FiniteHidden.{u,v} L → Prop} (hK : FullHereditary L K) :
    CCO.ResetOrder.Unary.Hereditary (resetUnaryAge L K) := by
  intro A B hA h
  obtain ⟨e⟩ := h
  exact hK hA (resetUnaryDecodeEmbedding L e)

theorem resetUnaryRamsey_of_fullCode {K : FiniteHidden.{u,v} L → Prop} (ramsey : HasHiddenRamsey K) :
    CCO.ResetOrder.Unary.Ramsey (resetUnaryAge L K) := by
  intro A B hA hB n hn
  obtain ⟨C,hC,arrow⟩ := ramsey (resetUnaryDecodeObject L A) (resetUnaryDecodeObject L B) hA hB n hn
  refine ⟨resetUnaryObject L C,hC,?_⟩
  intro color
  obtain ⟨g,shade,hg⟩ := arrow (fun f => color (resetUnaryEmbeddingOfDecode L f))
  refine ⟨resetUnaryEmbeddingOfDecode L g,shade,?_⟩
  intro f
  have he : CCO.ResetOrder.Unary.compose
      (resetUnaryEmbeddingOfDecode L (C := B.data) (D := (resetUnaryObject L C).data) g) f =
      resetUnaryEmbeddingOfDecode L (C := A.data) (D := (resetUnaryObject L C).data)
        (g.comp (resetUnaryDecodeEmbedding L f)) := CCO.ResetOrder.Unary.hom_ext (fun _ => rfl)
  exact (congrArg color he).trans (hg (resetUnaryDecodeEmbedding L f))

theorem fullCodeRamsey_of_resetUnary {K : FiniteHidden.{u,v} L → Prop}
    (ramsey : CCO.ResetOrder.Unary.Ramsey (resetUnaryAge L K)) : HasHiddenRamsey K := by
  intro A B hA hB n hn
  obtain ⟨C,hC,arrow⟩ := ramsey (resetUnaryObject L A) (resetUnaryObject L B) hA hB n hn
  refine ⟨resetUnaryDecodeObject L C,hC,?_⟩
  intro color
  obtain ⟨g,shade,hg⟩ := arrow (fun f => color (resetUnaryDecodeEmbedding L f))
  refine ⟨resetUnaryDecodeEmbedding L g,shade,?_⟩
  intro f
  have he : (resetUnaryDecodeEmbedding L g).comp f =
      resetUnaryDecodeEmbedding L (CCO.ResetOrder.Unary.compose g (resetUnaryEmbedding L f)) :=
    Structure.Embedding.ext (fun _ => rfl)
  exact (congrArg color he).trans (hg (resetUnaryEmbedding L f))

/-- Source C20's restriction theorem is the actual accepted B036
restriction, through the exact record codec; excluded sorts stay empty. -/
theorem fullCode_sort_restriction_ramsey (I : Set L.Sorts)
    (hI : ∀ F, L.input F ∈ I → L.output F ∈ I)
    {K : FiniteHidden.{u,v} L → Prop} (hK : FullHereditary L K) (ramsey : HasHiddenRamsey K) :
    HasHiddenRamsey (fun A => K A ∧ ∀ x, A.model.sort x ∈ I) := by
  apply fullCodeRamsey_of_resetUnary L
  exact CCO.ResetOrder.Unary.restriction_ramsey (L := resetUnarySignature L) (I := I) hI (resetUnaryAge_hereditary L hK)
    (resetUnaryRamsey_of_fullCode L ramsey)

end
end CCO.APRamseyReadout
