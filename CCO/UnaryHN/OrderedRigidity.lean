import CCO.UnaryHN.OrderedAmbient
import Mathlib.Order.Preorder.Finite

/-! Finite ordered copies have unique full embeddings on their fixed range.
This gives the actual copies/embeddings convention adapter, including an
empty source. -/

universe u v
namespace CCO.UnaryHN.Native

open StructuralRamsey
open StructuralRamsey.Structure

theorem ordered_self_embedding_eq_id {L : Language.{u}} {V : Type v}
    [Finite V] [LinearOrder V] (A : Structure L V)
    (e : Embedding A.withLinearOrder A.withLinearOrder) :
    e = Embedding.id A.withLinearOrder := by
  apply Embedding.ext
  intro x
  exact e.strictMono.apply_eq

theorem ordered_embedding_eq_of_range {L : Language.{u}} {V W : Type v}
    [Finite V] [LinearOrder V] [LinearOrder W] {A : Structure L V} {B : Structure L W}
    (e1 e2 : Embedding A.withLinearOrder B.withLinearOrder)
    (hRange : Set.range e1 = Set.range e2) : e1 = e2 := by
  let : Subsingleton (V ≃o V) := ⟨by
    intro f g
    apply OrderIso.ext
    funext x
    exact f.strictMono.apply_eq.trans g.strictMono.apply_eq.symm⟩
  have hFun : (e1 : V → W) = e2 := e1.strictMono.eq_of_range_eq e2.strictMono hRange
  exact Embedding.ext (congrFun hFun)

/-- Actual copies are the literal ranges of full ordered embeddings. -/
noncomputable def ordered_embedding_copy_equiv {L : Language.{u}} {V W : Type v}
    [Finite V] [LinearOrder V] [LinearOrder W] (A : Structure L V) (B : Structure L W) :
    Embedding A.withLinearOrder B.withLinearOrder ≃
      Set.range (fun e : Embedding A.withLinearOrder B.withLinearOrder => Set.range e) where
  toFun e := ⟨Set.range e, e, rfl⟩
  invFun S := Classical.choose S.2
  left_inv e := ordered_embedding_eq_of_range _ _ (Classical.choose_spec
    (show ∃ f : Embedding A.withLinearOrder B.withLinearOrder, Set.range f = Set.range e from ⟨e, rfl⟩))
  right_inv S := Subtype.ext (Classical.choose_spec S.2)

end CCO.UnaryHN.Native
