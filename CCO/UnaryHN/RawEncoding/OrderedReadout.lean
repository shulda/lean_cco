import CCO.UnaryHN.RawEncoding.Basic
import PartiteConstruction.Structure.Order

/-! The native ordered arrow is literally the arrow for typed induced maps
preserving the given strict order. No copies convention or transport premise. -/
universe u v w z k
namespace CCO.UnaryHN.Raw
open CCO.UnarySupport (Signature)
variable {L : Signature.{u}} {V : Type v} {W : Type w} {X : Type z}

structure OrderedEmbedding (A : Typed L V) (B : Typed L W)
    [LinearOrder V] [LinearOrder W] extends CCO.UnarySupport.Structure.Embedding A B where
  order_iff : ∀ x y, point x < point y ↔ x < y

@[ext] theorem OrderedEmbedding.ext {A : Typed L V} {B : Typed L W}
    [LinearOrder V] [LinearOrder W] {e f : OrderedEmbedding A B}
    (h : e.point = f.point) : e = f := by
  have hb : e.toEmbedding = f.toEmbedding := by
    apply (embeddingEquiv A B).injective
    apply StructuralRamsey.Structure.Embedding.ext
    intro x
    exact congrFun h x
  cases e
  cases f
  cases hb
  rfl

def encodeOrderedEmbedding {A : Typed L V} {B : Typed L W}
    [LinearOrder V] [LinearOrder W] (e : OrderedEmbedding A B) :
    StructuralRamsey.Structure.Embedding (encode A).withLinearOrder (encode B).withLinearOrder where
  toFun := e.point
  injective := e.injective
  map_rel_iff
    | .inl R, xs => (encodeEmbedding e.toEmbedding).map_rel_iff R xs
    | .inr _, xs => by
      change e.point (xs (0 : Fin 2)) < e.point (xs (1 : Fin 2)) ↔
        xs (0 : Fin 2) < xs (1 : Fin 2)
      exact e.order_iff _ _
  map_func := (encodeEmbedding e.toEmbedding).map_func

def decodeOrderedEmbedding {A : Typed L V} {B : Typed L W}
    [LinearOrder V] [LinearOrder W]
    (e : StructuralRamsey.Structure.Embedding (encode A).withLinearOrder (encode B).withLinearOrder) :
    OrderedEmbedding A B :=
  let old : StructuralRamsey.Structure.Embedding (encode A) (encode B) := {
    toFun := e
    injective := e.injective
    map_rel_iff R xs := e.map_rel_iff (.inl R) xs
    map_func := e.map_func }
  { toEmbedding := decodeEmbedding old
    order_iff x y := e.map_rel_iff (.inr ()) (![x, y] : Fin 2 → V) }

def orderedEmbeddingEquiv (A : Typed L V) (B : Typed L W)
    [LinearOrder V] [LinearOrder W] :
    OrderedEmbedding A B ≃
      StructuralRamsey.Structure.Embedding (encode A).withLinearOrder (encode B).withLinearOrder where
  toFun := encodeOrderedEmbedding
  invFun := decodeOrderedEmbedding
  left_inv e := by apply OrderedEmbedding.ext; rfl
  right_inv e := by apply StructuralRamsey.Structure.Embedding.ext; intro x; rfl

def OrderedEmbedding.compose {A : Typed L V} {B : Typed L W} {C : Typed L X}
    [LinearOrder V] [LinearOrder W] [LinearOrder X]
    (g : OrderedEmbedding B C) (f : OrderedEmbedding A B) : OrderedEmbedding A C :=
  decodeOrderedEmbedding ((encodeOrderedEmbedding g).comp (encodeOrderedEmbedding f))

def OrderedArrow (A : Typed L V) (B : Typed L W) (C : Typed L X)
    [LinearOrder V] [LinearOrder W] [LinearOrder X] (κ : Type k) : Prop :=
  ∀ χ : OrderedEmbedding A C → κ, ∃ g : OrderedEmbedding B C,
    ∀ e₁ e₂ : OrderedEmbedding A B, χ (g.compose e₁) = χ (g.compose e₂)

theorem decodeOrdered_comp {A : Typed L V} {B : Typed L W} {C : Typed L X}
    [LinearOrder V] [LinearOrder W] [LinearOrder X]
    (g : StructuralRamsey.Structure.Embedding (encode B).withLinearOrder (encode C).withLinearOrder)
    (f : OrderedEmbedding A B) :
    decodeOrderedEmbedding (g.comp (encodeOrderedEmbedding f)) =
      (decodeOrderedEmbedding g).compose f := by
  apply OrderedEmbedding.ext
  rfl

theorem encodeOrdered_comp_decode {A : Typed L V} {B : Typed L W} {C : Typed L X}
    [LinearOrder V] [LinearOrder W] [LinearOrder X]
    (g : OrderedEmbedding B C)
    (f : StructuralRamsey.Structure.Embedding (encode A).withLinearOrder (encode B).withLinearOrder) :
    encodeOrderedEmbedding (g.compose (decodeOrderedEmbedding f)) =
      (encodeOrderedEmbedding g).comp f := by
  apply StructuralRamsey.Structure.Embedding.ext
  intro x
  rfl

/-- Every colour is on ALL actual induced ordered vertex embeddings. -/
theorem orderedArrow_encode_iff (A : Typed L V) (B : Typed L W) (C : Typed L X)
    [LinearOrder V] [LinearOrder W] [LinearOrder X] (κ : Type k) :
    StructuralRamsey.Structure.Arrow (encode A).withLinearOrder (encode B).withLinearOrder
      (encode C).withLinearOrder κ ↔ OrderedArrow A B C κ := by
  constructor
  · intro h χ
    obtain ⟨g, hg⟩ := h (fun e => χ (decodeOrderedEmbedding e))
    refine ⟨decodeOrderedEmbedding g, ?_⟩
    intro e₁ e₂
    simpa only [decodeOrdered_comp] using hg (encodeOrderedEmbedding e₁) (encodeOrderedEmbedding e₂)
  · intro h χ
    obtain ⟨g, hg⟩ := h (fun e => χ (encodeOrderedEmbedding e))
    refine ⟨encodeOrderedEmbedding g, ?_⟩
    intro e₁ e₂
    simpa only [encodeOrdered_comp_decode] using hg (decodeOrderedEmbedding e₁) (decodeOrderedEmbedding e₂)

end CCO.UnaryHN.Raw
