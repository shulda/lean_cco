import CCO.UnaryHN.UnaryFunctions
import CCO.UnarySupport.HNDiagrams

/-! The literal one-sorted encoding of typed partial unary structures.
Sorts are positive unary predicates; every function graph and every old
relation tuple, including nullary truth, stays on the SAME carrier. -/
universe u v w
namespace CCO.UnaryHN.Raw

open CCO.UnarySupport (Signature)

abbrev language (L : Signature.{u}) : StructuralRamsey.Language.{u} where
  RelSymbol := L.Rel ⊕ L.Sorts
  FuncSymbol := L.Func
  relArity
    | .inl R => L.arity R
    | .inr _ => 1
  funcArity _ := 1

abbrev Typed (L : Signature.{u}) (V : Type v) := CCO.UnarySupport.Structure L V
abbrev Diagram (L : Signature.{u}) (V : Type v) := StructuralRamsey.Structure (language L) V

def encode {L : Signature.{u}} {V : Type v} (C : Typed L V) : Diagram L V where
  rel
    | .inl R, xs => C.rel R xs
    | .inr s, xs => C.sort (xs 0) = s
  func F xs := C.func F (xs 0)

theorem unary_language (L : Signature.{u}) : Native.Unary (language L) := fun _ => rfl

theorem singleton_encode {L : Signature.{u}} {V : Type v} (C : Typed L V) :
    (encode C).SingletonValued := fun F xs y z => C.functional F (xs 0) y z

theorem typed_ext {L : Signature.{u}} {V : Type v} {C D : Typed L V}
    (hs : C.sort = D.sort) (hf : C.func = D.func) (hr : C.rel = D.rel) : C = D := by
  cases C
  cases D
  cases hs
  cases hf
  cases hr
  rfl

theorem diagram_ext {L : Signature.{u}} {V : Type v} {C D : Diagram L V}
    (hr : C.rel = D.rel) (hf : C.func = D.func) : C = D := by
  cases C
  cases D
  cases hr
  cases hf
  rfl

theorem encode_injective {L : Signature.{u}} {V : Type v} :
    Function.Injective (encode (L := L) (V := V)) := by
  intro C D h
  apply typed_ext
  · funext x
    have hx : (encode D).rel (.inr (C.sort x)) (fun _ => x) := by
      rw [← h]
      rfl
    exact hx.symm
  · funext F x
    exact congrArg (fun E : Diagram L V => E.func F (fun _ => x)) h
  · funext R xs
    exact congrArg (fun E : Diagram L V => E.rel (.inl R) xs) h

def encodeEmbedding {L : Signature.{u}} {V : Type v} {W : Type w}
    {C : Typed L V} {D : Typed L W} (e : C.Embedding D) :
    StructuralRamsey.Structure.Embedding (encode C) (encode D) where
  toFun := e.point
  injective := e.injective
  map_rel_iff
    | .inl R, xs => ⟨e.reflect_rel R xs, e.map_rel R xs⟩
    | .inr s, xs => by change D.sort (e.point (xs 0)) = s ↔ C.sort (xs 0) = s; rw [e.sort_eq]
  map_func F xs := (e.map_func_eq F (xs 0)).symm

def decodeEmbedding {L : Signature.{u}} {V : Type v} {W : Type w}
    {C : Typed L V} {D : Typed L W}
    (e : StructuralRamsey.Structure.Embedding (encode C) (encode D)) : C.Embedding D where
  point := e
  sort_eq x := (e.map_rel_iff (.inr (C.sort x)) (fun _ => x)).mpr rfl
  map_func F x y hy := by
    have h : e y ∈ StructuralRamsey.Structure.imageSet e ((encode C).func F (fun _ => x)) :=
      ⟨y, hy, rfl⟩
    rw [e.map_func F (fun _ => x)] at h
    exact h
  map_rel R xs := (e.map_rel_iff (.inl R) xs).mpr
  injective := e.injective
  reflect_func F x y hy := by
    have h : y ∈ (encode D).func F (e ∘ (fun _ => x)) := hy
    rw [← e.map_func F (fun _ => x)] at h
    exact h
  reflect_rel R xs := (e.map_rel_iff (.inl R) xs).mp

/-- Literal vertex maps in both directions, not merely existence of some embedding. -/
def embeddingEquiv {L : Signature.{u}} {V : Type v} {W : Type w}
    (C : Typed L V) (D : Typed L W) :
    C.Embedding D ≃ StructuralRamsey.Structure.Embedding (encode C) (encode D) where
  toFun := encodeEmbedding
  invFun := decodeEmbedding
  left_inv e := by cases e; rfl
  right_inv e := by apply StructuralRamsey.Structure.Embedding.ext; intro x; rfl

theorem closed_encode_iff {L : Signature.{u}} {V : Type v} (C : Typed L V) (A : Set V) :
    (encode C).IsClosed A ↔ C.IsClosed A := by
  constructor
  · intro h F x hx y hy
    exact h F (fun _ => x) (fun _ => hx) hy
  · intro h F xs hx y hy
    exact h F (xs 0) (hx 0) hy

theorem encode_induce {L : Signature.{u}} {V : Type v} (C : Typed L V)
    (A : Set V) (hA : C.IsClosed A) :
    encode (C.induce A hA) = (encode C).induce A ((closed_encode_iff C A).mpr hA) := by
  apply diagram_ext
  · funext R xs
    cases R <;> rfl
  · rfl

theorem closure_encode {L : Signature.{u}} {V : Type v} (C : Typed L V) (A : Set V) :
    (encode C).functionClosure A = C.closure A := by
  apply Set.Subset.antisymm
  · intro x hx
    exact hx (C.closure A) ((closed_encode_iff C _).mpr (C.isClosed_closure A))
      (C.subset_closure A)
  · apply C.closure_minimal
      ((closed_encode_iff C _).mp ((encode C).functionClosure_isClosed A))
    exact (encode C).subset_functionClosure A

/-- ANY induced raw subobject of an encoded typed object has a concrete typed
presentation on its OWN carrier. The typing is derived from its actual embedding. -/
def pullbackTyped {L : Signature.{u}} {V : Type v} {W : Type w}
    (C : Typed L W) {A : Diagram L V}
    (e : StructuralRamsey.Structure.Embedding A (encode C)) : Typed L V where
  sort x := C.sort (e x)
  func F x := A.func F (fun _ => x)
  functional F x y z hy hz := by
    apply e.injective
    apply C.functional F (e x) (e y) (e z)
    · have h : e y ∈ StructuralRamsey.Structure.imageSet e (A.func F (fun _ => x)) :=
        ⟨y, hy, rfl⟩
      rw [e.map_func F (fun _ => x)] at h
      exact h
    · have h : e z ∈ StructuralRamsey.Structure.imageSet e (A.func F (fun _ => x)) :=
        ⟨z, hz, rfl⟩
      rw [e.map_func F (fun _ => x)] at h
      exact h
  func_sorted F x y hy := by
    apply C.func_sorted F (e x) (e y)
    have h : e y ∈ StructuralRamsey.Structure.imageSet e (A.func F (fun _ => x)) :=
      ⟨y, hy, rfl⟩
    rw [e.map_func F (fun _ => x)] at h
    exact h
  rel R xs := A.rel (.inl R) xs
  rel_sorted R xs hy := C.rel_sorted R (e ∘ xs) ((e.map_rel_iff (.inl R) xs).mpr hy)

theorem encode_pullbackTyped {L : Signature.{u}} {V : Type v} {W : Type w}
    (C : Typed L W) {A : Diagram L V}
    (e : StructuralRamsey.Structure.Embedding A (encode C)) :
    encode (pullbackTyped C e) = A := by
  apply diagram_ext
  · funext R xs
    apply propext
    cases R with
    | inl R => exact Iff.rfl
    | inr s => exact e.map_rel_iff (.inr s) xs
  · funext F xs
    have hx : (fun _ : Fin 1 => xs 0) = xs := by
      funext i
      have hi : i = 0 := Fin.eq_zero i
      subst i
      rfl
    change A.func F (fun _ => xs 0) = A.func F xs
    rw [hx]

def pullbackTypedEmbedding {L : Signature.{u}} {V : Type v} {W : Type w}
    (C : Typed L W) {A : Diagram L V}
    (e : StructuralRamsey.Structure.Embedding A (encode C)) :
    (pullbackTyped C e).Embedding C := by
  apply decodeEmbedding
  rw [encode_pullbackTyped]
  exact e

end CCO.UnaryHN.Raw
