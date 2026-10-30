import CCO.FullCode.CodeTransport
import Mathlib.Basic.Finite.Sum
import Mathlib.Basic.Finite.Prod

/-! The full code really is a finite unary/binary relational language.
Its induced embeddings are exactly the previously constructed code maps. -/
universe u v w a b
namespace CCO.FullCode
variable {L : Language.{u}} {V : Type v} {W : Type w}

def codeLanguage (N : NormalForms L) (S : RootScheme L) : Language.{u} where
  Sorts := PUnit
  Func := PEmpty
  Unary := S.Tag ⊕ (L.Unary × Presentation N S)
  Binary := (Presentation N S × Presentation N S) ⊕ (L.Binary × Presentation N S × Presentation N S)
  input F := PEmpty.elim F
  output F := PEmpty.elim F
  unarySort _ := PUnit.unit
  leftSort _ := PUnit.unit
  rightSort _ := PUnit.unit
  finiteSort := inferInstance
  finiteFunc := inferInstance
  finiteUnary := inferInstance
  finiteBinary := inferInstance

namespace Object
variable {C : Structure L V} {D : Structure L W} {S : RootScheme L}
  {A : Type a} {B : Type b}

def codeStructure (O : Object C S A) (N : NormalForms L) : Structure (codeLanguage N S) A where
  sort _ := PUnit.unit
  func F := PEmpty.elim F
  functional F := PEmpty.elim F
  func_sorted F := PEmpty.elim F
  unary U a := match U with
    | .inl tag => (O.root a).tag = tag
    | .inr (U, p) => UnaryCode N U (O.root a) p
  unary_sorted _ _ _ := rfl
  binary R a b := match R with
    | .inl (p, q) => EqualityCode N (O.root a) (O.root b) p q
    | .inr (R, p, q) => BinaryCode N R (O.root a) (O.root b) p q
  binary_sorted _ _ _ _ := ⟨rfl, rfl⟩

def Embedding.asCodeEmbedding {N : NormalForms L} {O : Object C S A} {P : Object D S B}
    (f : Embedding N O P) : Structure.Embedding (O.codeStructure N) (P.codeStructure N) where
  point := f.point
  injective := f.injective
  sort_eq _ := rfl
  map_func F := PEmpty.elim F
  reflect_func F := PEmpty.elim F
  unary_iff U a := by
    cases U with
    | inl tag => change (P.root (f.point a)).tag = tag ↔ (O.root a).tag = tag; rw [f.tag_eq a]
    | inr U => exact f.unary_iff U.1 a U.2
  binary_iff R a b := by
    cases R with
    | inl ps => exact f.equality_iff a b ps.1 ps.2
    | inr ps => exact f.binary_iff ps.1 a b ps.2.1 ps.2.2

def embeddingOfCode {N : NormalForms L} {O : Object C S A} {P : Object D S B}
    (f : Structure.Embedding (O.codeStructure N) (P.codeStructure N)) : Embedding N O P where
  point := f.point
  injective := f.injective
  tag_eq a := (f.unary_iff (.inl (O.root a).tag) a).mpr rfl
  equality_iff a b p q := f.binary_iff (.inl (p, q)) a b
  unary_iff U a p := f.unary_iff (.inr (U, p)) a
  binary_iff R a b p q := f.binary_iff (.inr (R, p, q)) a b

def codeEmbeddingEquiv (N : NormalForms L) (O : Object C S A) (P : Object D S B) :
    Embedding N O P ≃ Structure.Embedding (O.codeStructure N) (P.codeStructure N) where
  toFun := Embedding.asCodeEmbedding
  invFun := embeddingOfCode
  left_inv _f := Embedding.ext (fun _ => rfl)
  right_inv _f := Structure.Embedding.ext (fun _ => rfl)

end Object
end CCO.FullCode
