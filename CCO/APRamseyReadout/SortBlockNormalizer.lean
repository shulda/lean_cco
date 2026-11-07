import CCO.APRamseyReadout.ResetCodecs
import CCO.APRamseyReadout.SortBlockOrder
import Mathlib.Basic.Finite.Sum
import Mathlib.Basic.Finite.Prod

/-! Independent A04/C41--46: legal all-order replacements form a strict
same-map idempotent endofunctor. Its hereditary Ramsey fixed class is an
actual application of B036, without clone, SAP, CCO or term premises. -/

universe u v w
namespace CCO.APRamseyReadout
open CCO.FullCode
noncomputable section
variable (L : Language.{u})

abbrev blockLanguage : Language.{u} where
  Sorts := L.Sorts
  Func := L.Func
  Unary := L.Unary
  Binary := L.Binary ⊕ (L.Sorts × L.Sorts)
  input := L.input
  output := L.output
  unarySort := L.unarySort
  leftSort R := match R with | .inl R => L.leftSort R | .inr p => p.1
  rightSort R := match R with | .inl R => L.rightSort R | .inr p => p.2
  finiteSort := L.finiteSort
  finiteFunc := L.finiteFunc
  finiteUnary := L.finiteUnary
  finiteBinary := inferInstance

def blockReduct {V : Type v} (C : Structure (blockLanguage L) V) : Structure L V where
  sort := C.sort
  func := C.func
  functional := C.functional
  func_sorted := C.func_sorted
  unary := C.unary
  unary_sorted := C.unary_sorted
  binary R := C.binary (.inl R)
  binary_sorted R := C.binary_sorted (.inl R)

def blockStructure {V : Type v} (C : Structure L V) (o : LinearOrder V) :
    Structure (blockLanguage L) V where
  sort := C.sort
  func := C.func
  functional := C.functional
  func_sorted := C.func_sorted
  unary := C.unary
  unary_sorted := C.unary_sorted
  binary R x y := match R with
    | .inl R => C.binary R x y
    | .inr p => C.sort x = p.1 ∧ C.sort y = p.2 ∧ @LT.lt V o.toLT x y
  binary_sorted R x y h := by
    cases R with
    | inl R => exact C.binary_sorted R x y h
    | inr p => exact ⟨h.1,h.2.1⟩

@[simp] theorem blockReduct_structure {V : Type v} (C : Structure L V) (o : LinearOrder V) :
    blockReduct L (blockStructure L C o) = C := rfl

variable (priority : LinearOrder L.Sorts)

/-- Defined on ALL structures, so malformed order predicates need no
arbitrary selected linear order. Every other datum remains literal. -/
def blockNormalize {V : Type v} (C : Structure (blockLanguage L) V) : Structure (blockLanguage L) V where
  sort := C.sort
  func := C.func
  functional := C.functional
  func_sorted := C.func_sorted
  unary := C.unary
  unary_sorted := C.unary_sorted
  binary R x y := match R with
    | .inl R => C.binary (.inl R) x y
    | .inr p => C.sort x = p.1 ∧ C.sort y = p.2 ∧
      (@LT.lt _ priority.toLT p.1 p.2 ∨ (p.1 = p.2 ∧ C.binary (.inr p) x y))
  binary_sorted R x y h := by
    cases R with
    | inl R => exact C.binary_sorted (.inl R) x y h
    | inr p => exact ⟨h.1,h.2.1⟩

private theorem fullStructure_ext {V : Type v} {C D : Structure L V}
    (hs : C.sort = D.sort) (hf : C.func = D.func) (hu : C.unary = D.unary)
    (hb : C.binary = D.binary) : C = D := by
  cases C; cases D; cases hs; cases hf; cases hu; cases hb; rfl

@[simp] theorem blockReduct_normalize {V : Type v} (C : Structure (blockLanguage L) V) :
    blockReduct L (blockNormalize L priority C) = blockReduct L C := rfl

/-- On legal ordered objects this is exactly the global concatenation
of unchanged within-sort restrictions. -/
theorem blockNormalize_structure {V : Type v} (C : Structure L V) (o : LinearOrder V) :
    blockNormalize L priority (blockStructure L C o) =
      blockStructure L C (sortBlockOrder C.sort priority o) := by
  apply fullStructure_ext (blockLanguage L)
    (C := blockNormalize L priority (blockStructure L C o))
    (D := blockStructure L C (sortBlockOrder C.sort priority o)) rfl rfl rfl
  funext R x y
  cases R with
  | inl R => rfl
  | inr p =>
    apply propext
    change (C.sort x = p.1 ∧ C.sort y = p.2 ∧
      (@LT.lt _ priority.toLT p.1 p.2 ∨
        (p.1 = p.2 ∧ C.sort x = p.1 ∧ C.sort y = p.2 ∧ @LT.lt _ o.toLT x y))) ↔
      (C.sort x = p.1 ∧ C.sort y = p.2 ∧
        @LT.lt _ (sortBlockOrder C.sort priority o).toLT x y)
    rw [sortBlockOrder_lt_iff]
    constructor
    · rintro ⟨hx,hy,h⟩
      exact ⟨hx,hy,by simpa only [hx,hy] using h.imp_right (fun ht => ⟨ht.1,ht.2.2.2⟩)⟩
    · rintro ⟨hx,hy,h⟩
      refine ⟨hx,hy,?_⟩
      rw [hx,hy] at h
      exact h.imp_right (fun ht => ⟨ht.1,hx,hy,ht.2⟩)

/-- Strict idempotence holds globally, before any age-membership proof. -/
theorem blockNormalize_idempotent {V : Type v} (C : Structure (blockLanguage L) V) :
    blockNormalize L priority (blockNormalize L priority C) = blockNormalize L priority C := by
  apply fullStructure_ext (blockLanguage L)
    (C := blockNormalize L priority (blockNormalize L priority C))
    (D := blockNormalize L priority C) rfl rfl rfl
  funext R x y
  cases R with
  | inl R => rfl
  | inr p =>
    apply propext
    letI := priority
    by_cases he : p.1 = p.2
    · simp only [blockNormalize,he,lt_self_iff_false,false_or,true_and]
      constructor
      · rintro ⟨hx,hy,_,_,hr⟩
        exact ⟨hx,hy,hr⟩
      · rintro ⟨hx,hy,hr⟩
        exact ⟨hx,hy,hx,hy,hr⟩
    · simp only [blockNormalize,he,false_and,or_false]

def blockNormalizeEmbedding {V : Type v} {W : Type w}
    {C : Structure (blockLanguage L) V} {D : Structure (blockLanguage L) W}
    (e : Structure.Embedding C D) :
    Structure.Embedding (blockNormalize L priority C) (blockNormalize L priority D) where
  point := e.point
  injective := e.injective
  sort_eq := e.sort_eq
  map_func := e.map_func
  reflect_func := e.reflect_func
  unary_iff := e.unary_iff
  binary_iff R x y := by
    cases R with
    | inl R => exact e.binary_iff (.inl R) x y
    | inr p =>
      change (D.sort (e.point x) = p.1 ∧ D.sort (e.point y) = p.2 ∧
        (@LT.lt _ priority.toLT p.1 p.2 ∨ (p.1 = p.2 ∧ D.binary (.inr p) (e.point x) (e.point y)))) ↔ _
      rw [e.sort_eq x,e.sort_eq y,e.binary_iff (.inr p) x y]
      rfl

/-- Every allowed unordered reduct admits EVERY actual global order. -/
def allBlockOrders (K : FiniteHidden.{u,v} L → Prop)
    (A : FiniteHidden.{u,v} (blockLanguage L)) : Prop :=
  ∃ (C : Structure L A.Carrier) (o : LinearOrder A.Carrier),
    K ⟨A.Carrier,C,A.finite⟩ ∧ A.model = blockStructure L C o

def blockFixedAge (K : FiniteHidden.{u,v} L → Prop)
    (A : FiniteHidden.{u,v} (blockLanguage L)) : Prop :=
  allBlockOrders L K A ∧ blockNormalize L priority A.model = A.model

theorem blockNormalize_member {K : FiniteHidden.{u,v} L → Prop}
    (A : FiniteHidden.{u,v} (blockLanguage L)) (hA : allBlockOrders L K A) :
    allBlockOrders L K ⟨A.Carrier,blockNormalize L priority A.model,A.finite⟩ := by
  obtain ⟨C,o,hC,he⟩ := hA
  refine ⟨C,sortBlockOrder C.sort priority o,hC,?_⟩
  exact (congrArg (blockNormalize L priority) he).trans (blockNormalize_structure L priority C o)

/-- The actual B036 normalizer, with identity carrier and vertex maps. -/
def sortBlockNormalizer (K : FiniteHidden.{u,v} L → Prop) :
    CCO.ResetOrder.Generic.Normalizer (resetAge (blockLanguage L) (allBlockOrders L K)) where
  normalize A := resetStructure (blockLanguage L)
    (blockNormalize L priority (resetDecode (blockLanguage L) A.data))
  member A hA := blockNormalize_member L priority (resetDecodeObject (blockLanguage L) A) hA
  map hA hB e := resetEmbeddingOfDecode (blockLanguage L)
    (blockNormalizeEmbedding L priority (resetDecodeEmbedding (blockLanguage L) e))
  map_point _ _ e := resetEmbeddingOfDecode_point (blockLanguage L) _
  idempotent A _ := congrArg (resetStructure (blockLanguage L))
    (blockNormalize_idempotent L priority (resetDecode (blockLanguage L) A.data))

theorem sortBlockNormalizer_fixedClass (K : FiniteHidden.{u,v} L → Prop) :
    (sortBlockNormalizer L priority K).fixedClass = resetAge (blockLanguage L) (blockFixedAge L priority K) := by
  funext A
  apply propext
  constructor
  · rintro ⟨hA,hf⟩
    refine ⟨hA,?_⟩
    exact congrArg (resetDecode (blockLanguage L)) hf
  · rintro ⟨hA,hf⟩
    refine ⟨hA,?_⟩
    exact (congrArg (resetStructure (blockLanguage L)) hf).trans
      (resetStructure_resetDecode (blockLanguage L) A.data)

/-- C41--46: concrete same-map normalization, legality and strict
idempotence discharge every B036 normalizer field internally. -/
theorem sort_block_normalization (K : FiniteHidden.{u,v} L → Prop)
    (hereditary : FullHereditary (blockLanguage L) (allBlockOrders L K))
    (ramsey : HasHiddenRamsey (allBlockOrders L K)) :
    FullHereditary (blockLanguage L) (blockFixedAge L priority K) ∧
      HasHiddenRamsey (blockFixedAge L priority K) := by
  let N := sortBlockNormalizer L priority K
  have hh : CCO.ResetOrder.Generic.Hereditary (resetLanguage (blockLanguage L)) N.fixedClass :=
    N.hereditary (resetAge_hereditary (blockLanguage L) hereditary)
  have hr : CCO.ResetOrder.Generic.Ramsey (resetLanguage (blockLanguage L)) N.fixedClass :=
    N.ramsey (resetRamsey_of_fullCode (blockLanguage L) ramsey)
  dsimp only [N] at hh hr
  rw [sortBlockNormalizer_fixedClass L priority K] at hh hr
  refine ⟨?_,fullCodeRamsey_of_reset (blockLanguage L) hr⟩
  intro A B hB e
  exact hh (A := resetObject (blockLanguage L) A) (B := resetObject (blockLanguage L) B)
    hB (resetEmbedding (blockLanguage L) e)

end
end CCO.APRamseyReadout
