import CCO.ResetOrder.Hierarchy.Reversal

/-! Actual partial-function diagrams and induced embeddings. All old domains,
values and arbitrary-arity relations remain literally unchanged by N. -/
universe u v w
namespace CCO.ResetOrder.Hierarchy
structure OldLanguage (I : Type u) where
  Func : I → I → Type u
  Rel : (n : ℕ) → (Fin n → I) → Type u

structure Diagram {I : Type u} (L : OldLanguage I) (X : I → Type v) where
  func : ∀ {i j}, L.Func i j → X i → Set (X j)
  functional : ∀ {i j} (F : L.Func i j) x y z, y ∈ func F x → z ∈ func F x → y = z
  rel : ∀ {n} {sorts : Fin n → I}, L.Rel n sorts → ((a : Fin n) → X (sorts a)) → Prop

namespace Diagram
variable {I : Type u} {L : OldLanguage I} {X : I → Type v} {Y : I → Type w}
structure Embedding (A : Diagram L X) (B : Diagram L Y) where
  point : ∀ i, X i → Y i
  injective : ∀ i, Function.Injective (point i)
  function_iff : ∀ {i j} (F : L.Func i j) x y,
    y ∈ B.func F (point i x) ↔ ∃ z, z ∈ A.func F x ∧ point j z = y
  relation_iff : ∀ {n} {sorts : Fin n → I} (R : L.Rel n sorts) xs,
    B.rel R (fun a => point (sorts a) (xs a)) ↔ A.rel R xs

namespace Embedding
@[ext] theorem ext {A : Diagram L X} {B : Diagram L Y} {f g : Embedding A B}
    (h : f.point = g.point) : f = g := by
  cases f; cases g
  cases h
  rfl

def identity (A : Diagram L X) : Embedding A A where
  point _ := id
  injective _ := Function.injective_id
  function_iff F x y := by simp
  relation_iff _ _ := Iff.rfl

def compose {A : Diagram L X} {B : Diagram L Y} {Z : I → Type*} {C : Diagram L Z}
    (g : Embedding B C) (f : Embedding A B) : Embedding A C where
  point i := g.point i ∘ f.point i
  injective i := (g.injective i).comp (f.injective i)
  function_iff F x y := by
    change y ∈ C.func F (g.point _ (f.point _ x)) ↔ _
    rw [g.function_iff]
    constructor
    · rintro ⟨b, hb, he⟩
      obtain ⟨a, ha, hab⟩ := (f.function_iff F x b).1 hb
      exact ⟨a, ha, by change g.point _ (f.point _ a) = y; rw [hab]; exact he⟩
    · rintro ⟨a, ha, he⟩
      exact ⟨f.point _ a, (f.function_iff F x _).2 ⟨a, ha, rfl⟩, he⟩
  relation_iff R xs := by
    exact (g.relation_iff R (fun a => f.point _ (xs a))).trans (f.relation_iff R xs)
end Embedding
end Diagram

namespace Charting
variable {R : Type u} {J : R → Type u} {H : Schedule (Sigma J)}
variable {X : Sigma J → Type v} {Y : Sigma J → Type w}
variable {S : System H X} {T : System H Y} {representative : ∀ r, J r}
variable (C : Charting S representative) (D : Charting T representative)
variable (L : OldLanguage (Sigma J))

structure OrderedStructure (C : Charting S representative) (L : OldLanguage (Sigma J)) where
  data : Diagram L X
  orders : S.Orders

namespace OrderedStructure
variable {C L}
@[ext] theorem ext {A B : OrderedStructure C L} (hd : A.data = B.data)
    (ho : A.orders = B.orders) : A = B := by
  cases A; cases B
  cases hd; cases ho
  rfl

noncomputable def normalize (A : OrderedStructure C L) : OrderedStructure C L :=
  ⟨A.data, C.normalize A.orders⟩

theorem normalize_idempotent (A : OrderedStructure C L) : A.normalize.normalize = A.normalize := by
  apply ext (A := A.normalize.normalize) (B := A.normalize)
  · rfl
  · exact C.normalize_idempotent A.orders
end OrderedStructure

structure OrderedEmbedding (A : OrderedStructure C L) (B : OrderedStructure D L) where
  old : Diagram.Embedding A.data B.data
  up_commute : ∀ i a x, T.up i a (old.point i x) = old.point (H.coordinate i a) (S.up i a x)
  chart_commute : ∀ r j x,
    D.back r j (old.point ⟨r,j⟩ x) = old.point ⟨r,representative r⟩ (C.back r j x)
  order_preserve : ∀ i x y, (A.orders i).lt x y → (B.orders i).lt (old.point i x) (old.point i y)

namespace OrderedEmbedding
variable {C D L} {A : OrderedStructure C L} {B : OrderedStructure D L}

theorem order_iff (f : OrderedEmbedding C D L A B) (i : Sigma J) (x y : X i) :
    (B.orders i).lt (f.old.point i x) (f.old.point i y) ↔ (A.orders i).lt x y := by
  constructor
  · intro h
    by_cases he : x = y
    · subst y
      exact False.elim ((B.orders i).irrefl _ h)
    · rcases (A.orders i).total he with hxy | hyx
      · exact hxy
      · exact False.elim ((B.orders i).asymm h (f.order_preserve i y x hyx))
  · exact f.order_preserve i x y

def geometryMap (f : OrderedEmbedding C D L A B) : S.Map T :=
  ⟨f.old.point, f.old.injective, f.up_commute⟩

theorem localTasks_preserve (f : OrderedEmbedding C D L A B) (i : Sigma J) (x y : X i)
    (h : (C.localTasks A.orders i).lt x y) :
    (D.localTasks B.orders i).lt (f.old.point i x) (f.old.point i y) := by
  obtain ⟨r,j⟩ := i
  refine ⟨(f.geometryMap.parent_iff _ x y).2 h.1, ?_⟩
  change (B.orders _).lt (D.back r j (f.old.point _ x)) (D.back r j (f.old.point _ y))
  rw [f.chart_commute, f.chart_commute]
  exact f.order_preserve _ _ _ h.2

noncomputable def normalize (f : OrderedEmbedding C D L A B) :
    OrderedEmbedding C D L A.normalize B.normalize where
  old := f.old
  up_commute := f.up_commute
  chart_commute := f.chart_commute
  order_preserve := f.geometryMap.normalize_preserves _ _ f.localTasks_preserve

theorem normalized_order_iff (f : OrderedEmbedding C D L A B) (i : Sigma J) (x y : X i) :
    (B.normalize.orders i).lt (f.old.point i x) (f.old.point i y) ↔
      (A.normalize.orders i).lt x y := f.geometryMap.normalize_reflects _ _ f.localTasks_preserve i x y

def identity (A : OrderedStructure C L) : OrderedEmbedding C C L A A where
  old := Diagram.Embedding.identity A.data
  up_commute _ _ _ := rfl
  chart_commute _ _ _ := rfl
  order_preserve _ _ _ h := h

def compose {Z : Sigma J → Type*} {U : System H Z} {E : Charting U representative}
    {B : OrderedStructure D L} {F : OrderedStructure E L}
    (g : OrderedEmbedding D E L B F) (f : OrderedEmbedding C D L A B) : OrderedEmbedding C E L A F where
  old := g.old.compose f.old
  up_commute i a x := by
    change U.up i a (g.old.point i (f.old.point i x)) = _
    rw [g.up_commute, f.up_commute]
    rfl
  chart_commute r j x := by
    change E.back r j (g.old.point _ (f.old.point _ x)) = _
    rw [g.chart_commute, f.chart_commute]
    rfl
  order_preserve i x y h := g.order_preserve i _ _ (f.order_preserve i x y h)

@[ext] theorem ext {f g : OrderedEmbedding C D L A B} (h : f.old = g.old) : f = g := by
  cases f; cases g
  cases h
  rfl

theorem normalize_identity (A : OrderedStructure C L) :
    (identity A).normalize = identity A.normalize := by
  apply ext
  rfl

theorem normalize_compose {Z : Sigma J → Type*} {U : System H Z} {E : Charting U representative}
    {B : OrderedStructure D L} {F : OrderedStructure E L}
    (g : OrderedEmbedding D E L B F) (f : OrderedEmbedding C D L A B) :
    (g.compose f).normalize = g.normalize.compose f.normalize := by
  apply ext
  rfl
end OrderedEmbedding
end Charting
end CCO.ResetOrder.Hierarchy
