import CCO.UnaryHN.UniversalEdge.TupleSupport

/-! Literal universal-edge expansion and the explicit completed-map
rigidity premise. Forgetting the edge is not claimed to preserve
irreducibility. All maps below keep their original vertex functions. -/

universe u v
namespace CCO.UnaryHN.Native

open StructuralRamsey
open StructuralRamsey.Structure

def edgeLanguage (L : Language.{u}) : Language.{u} where
  RelSymbol := L.RelSymbol ⊕ Unit
  FuncSymbol := L.FuncSymbol
  relArity := Sum.elim L.relArity (fun _ => 2)
  funcArity := L.funcArity

def expandEdge {L : Language.{u}} {V : Type v} (C : Structure L V) :
    Structure (edgeLanguage L) V where
  rel := by
    intro R xs
    cases R with
    | inl R => exact C.rel R xs
    | inr r =>
      change Fin 2 → V at xs
      exact xs 0 ≠ xs 1
  func := C.func

def edgeReduct {L : Language.{u}} {V : Type v}
    (C : Structure (edgeLanguage L) V) : Structure L V where
  rel R := C.rel (.inl R)
  func := C.func

@[simp] theorem edgeReduct_expandEdge {L : Language.{u}} {V : Type v}
    (C : Structure L V) : edgeReduct (expandEdge C) = C := rfl

def ExpandedClass {L : Language.{u}} (K : Class.{u,v} L) :
    Class.{u,v} (edgeLanguage L) :=
  fun {_} C => ∃ old : Structure L _, K old ∧ C = expandEdge old

theorem ExpandedClass.reduct_mem {L : Language.{u}} {K : Class.{u,v} L}
    {V : Type v} {C : Structure (edgeLanguage L) V}
    (hC : ExpandedClass K C) : K (edgeReduct C) := by
  obtain ⟨old, hOld, rfl⟩ := hC
  exact hOld

theorem ExpandedClass.edge_iff {L : Language.{u}} {K : Class.{u,v} L}
    {V : Type v} {C : Structure (edgeLanguage L) V}
    (hC : ExpandedClass K C) (xs : Fin 2 → V) :
    C.rel (.inr ()) xs ↔ xs 0 ≠ xs 1 := by
  obtain ⟨old, _, rfl⟩ := hC
  exact Iff.rfl

def reductEmbedding {L : Language.{u}} {V W : Type v}
    {C : Structure (edgeLanguage L) V} {D : Structure (edgeLanguage L) W}
    (e : Embedding C D) : Embedding (edgeReduct C) (edgeReduct D) where
  toFun := e
  injective := e.injective
  map_rel_iff R xs := e.map_rel_iff (.inl R) xs
  map_func := e.map_func

/-- C04: restriction to the actual closed structure is still the same HE. -/
theorem HE.restrict_closed {L : Language.{u}} {V W : Type v}
    {C : Structure L V} {D : Structure L W} {f : V → W}
    (hf : HE C D f) (S : Set V) (hS : C.IsClosed S) :
    HE (C.induce S hS) D (f ∘ Subtype.val) :=
  hf.comp (inclusion C S hS).isEHNHomomorphismEmbedding

/-- The explicit source A04 hypothesis, on whole actual completed members. -/
def CompletedMapRigidity {L : Language.{u}} (K : Class.{u,v} L) : Prop :=
  ∀ {V W : Type v} (C : Structure L V) (D : Structure L W),
    K C → K D → ∀ f : V → W, HE C D f →
      ∃ e : Embedding C D, ∀ x, e x = f x

/-- C10: an HE embeds its whole completed irreducible source. -/
theorem completedMapRigidity_of_irreducible {L : Language.{u}}
    {K : Class.{u,v} L} (hK : AllIrreducible K) : CompletedMapRigidity K := by
  intro V W C D hC _ f hf
  exact hf.2 C (hK C hC) (Embedding.id C)

/-- The alternative C10 sufficient hypothesis on completed homomorphisms. -/
theorem completedMapRigidity_of_homomorphisms {L : Language.{u}}
    {K : Class.{u,v} L}
    (hK : ∀ {V W : Type v} (C : Structure L V) (D : Structure L W),
      K C → K D → ∀ f : V → W, C.IsWeakHomomorphism D f →
        ∃ e : Embedding C D, ∀ x, e x = f x) : CompletedMapRigidity K :=
  fun C D hC hD f hf => hK C D hC hD f hf.1

end CCO.UnaryHN.Native
