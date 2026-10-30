import CCO.ResetOrder.Unary.Primitive.Basic
import Mathlib.Logic.Relation
import Mathlib.Data.Set.Lattice.Indexed

universe u v
namespace CCO.ResetOrder.Unary.Primitive.Structure
variable {L : Signature.{u}} {V : Type v} (C : Structure L V)

def Step (x y : V) : Prop := ∃ F, y ∈ C.func F x

def closure (B : Set V) : Set V :=
  {y | ∃ x ∈ B, Relation.ReflTransGen C.Step x y}

def closureAt (x : V) : Set V := C.closure {x}

theorem subset_closure (B : Set V) : B ⊆ C.closure B := by
  intro x hx
  exact ⟨x, hx, .refl⟩

theorem isClosed_closure (B : Set V) : C.IsClosed (C.closure B) := by
  rintro F y ⟨x, hx, hxy⟩ z hz
  exact ⟨x, hx, hxy.tail ⟨F, hz⟩⟩

theorem closure_minimal {B S : Set V} (hS : C.IsClosed S) (hBS : B ⊆ S) :
    C.closure B ⊆ S := by
  rintro y ⟨x, hx, hxy⟩
  have hstart := hBS hx
  induction hxy with
  | refl => exact hstart
  | tail h hstep ih =>
    obtain ⟨F, hF⟩ := hstep
    exact hS F _ ih hF

theorem closure_mono {B S : Set V} (h : B ⊆ S) : C.closure B ⊆ C.closure S :=
  C.closure_minimal (C.isClosed_closure S) (h.trans (C.subset_closure S))

theorem closure_eq {S : Set V} (hS : C.IsClosed S) : C.closure S = S :=
  Set.Subset.antisymm (C.closure_minimal hS (Set.Subset.refl _)) (C.subset_closure S)

theorem isClosed_empty : C.IsClosed ∅ := by
  intro F x hx
  exact False.elim hx

theorem isClosed_univ : C.IsClosed Set.univ := by
  intro F x hx y hy
  trivial

theorem isClosed_inter {S T : Set V} (hS : C.IsClosed S) (hT : C.IsClosed T) :
    C.IsClosed (S ∩ T) := by
  intro F x hx y hy
  exact ⟨hS F x hx.1 hy, hT F x hx.2 hy⟩

theorem isClosed_sUnion {A : Set (Set V)} (hA : ∀ S ∈ A, C.IsClosed S) :
    C.IsClosed (⋃₀ A) := by
  rintro F x ⟨S, hSA, hxS⟩ y hy
  exact ⟨S, hSA, hA S hSA F x hxS hy⟩

theorem closure_empty : C.closure ∅ = ∅ := C.closure_eq C.isClosed_empty

theorem closure_union (B S : Set V) : C.closure (B ∪ S) = C.closure B ∪ C.closure S := by
  ext y
  constructor
  · rintro ⟨x, hx | hx, hxy⟩
    · exact Or.inl ⟨x, hx, hxy⟩
    · exact Or.inr ⟨x, hx, hxy⟩
  · rintro (⟨x, hx, hxy⟩ | ⟨x, hx, hxy⟩)
    · exact ⟨x, Or.inl hx, hxy⟩
    · exact ⟨x, Or.inr hx, hxy⟩

theorem closure_singletons (B : Set V) : C.closure B = ⋃ x ∈ B, C.closureAt x := by
  ext y
  simp only [Set.mem_iUnion, closure, closureAt, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨x, hx, hxy⟩
    exact ⟨x, hx, x, rfl, hxy⟩
  · rintro ⟨x, hx, z, hzx, hzy⟩
    exact ⟨x, hx, hzx ▸ hzy⟩

theorem mem_closureAt (x : V) : x ∈ C.closureAt x := C.subset_closure {x} (by rfl)

end CCO.ResetOrder.Unary.Primitive.Structure
