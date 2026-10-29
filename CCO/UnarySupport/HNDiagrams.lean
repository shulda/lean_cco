import CCO.UnarySupport.Irreducible
import Mathlib.Data.Fintype.EquivFin

/-! Actual completed unary-generated diagrams. The class premise is about
these EXISTING full induced structures, including every relation and every
partial-function domain. It is not a completion or ambient-membership premise. -/

universe u v w
namespace CCO.UnarySupport.Structure

variable {L : Signature.{u}} {V : Type v} {W : Type w}

/-- A signature class, independent of the particular finite carrier. -/
abbrev Class (L : Signature.{u}) := {X : Type v} → Structure L X → Prop

def CompletedClass (K : Class.{u,v} L) : Prop :=
  ∀ {X : Type v} [Finite X] (D : Structure L X), K D → D.Total

def IrreduciblesIn (C : Structure L V) (K : Class.{u,v} L) : Prop :=
  ∀ (S : Set V) (hS : C.IsClosed S), (C.induce S hS).Irreducible → K (C.induce S hS)

def OneGenerated (C : Structure L V) : Prop := ∃ x : V, C.closure {x} = Set.univ

/-- Literal isomorphism of the whole typed domain/function/relation diagram. -/
structure DiagramIso (C : Structure L V) (D : Structure L W) where
  equiv : V ≃ W
  sort_eq : ∀ x, D.sort (equiv x) = C.sort x
  func_iff : ∀ F x y, equiv y ∈ D.func F (equiv x) ↔ y ∈ C.func F x
  rel_iff : ∀ R xs, D.rel R (equiv ∘ xs) ↔ C.rel R xs

def DiagramIso.refl (C : Structure L V) : DiagramIso C C where
  equiv := Equiv.refl V
  sort_eq _ := rfl
  func_iff _ _ _ := Iff.rfl
  rel_iff _ _ := Iff.rfl

def DiagramIso.toEmbedding {C : Structure L V} {D : Structure L W}
    (f : DiagramIso C D) : Embedding C D where
  point := f.equiv
  sort_eq := f.sort_eq
  map_func F x y h := (f.func_iff F x y).mpr h
  map_rel R xs h := (f.rel_iff R xs).mpr h
  injective := f.equiv.injective
  reflect_func F x y h := by
    refine ⟨f.equiv.symm y,?_,f.equiv.apply_symm_apply y⟩
    apply (f.func_iff F x (f.equiv.symm y)).mp
    simpa only [Equiv.apply_symm_apply] using h
  reflect_rel R xs h := (f.rel_iff R xs).mp h

/-- C20: this is membership of the entire actual induced singleton closure. -/
theorem singleton_mem_class (C : Structure L V) {K : Class.{u,v} L}
    (hK : C.IrreduciblesIn K) (x : V) : K (C.singletonStructure x) :=
  hK (C.closureAt x) (C.isClosed_closure {x}) (C.singleton_irreducible x)

theorem singleton_oneGenerated (C : Structure L V) (x : V) :
    (C.singletonStructure x).OneGenerated :=
  ⟨⟨x,C.mem_closureAt x⟩,C.singleton_generated x⟩

/-- C21: recognizing completed singleton diagrams creates NO new value. -/
theorem total_of_irreducibles [Finite V] (C : Structure L V) {K : Class.{u,v} L}
    (hCompleted : CompletedClass K) (hK : C.IrreduciblesIn K) : C.Total := by
  intro F x hx
  have hT := hCompleted (C.singletonStructure x) (C.singleton_mem_class hK x)
  obtain ⟨y,hy⟩ := hT F ⟨x,C.mem_closureAt x⟩ hx
  exact ⟨y.val,hy⟩

/-- Full local unary admissibility, with an actual finite completed
one-generated member and an isomorphism retaining ALL internal relations. -/
def FullUnaryAdmissible (C : Structure L V) (K : Class.{u,v} L) : Prop :=
  ∀ x : V, ∃ (X : Type v) (D : Structure L X), Finite X ∧ K D ∧
    D.Total ∧ D.OneGenerated ∧ Nonempty (DiagramIso (C.singletonStructure x) D)

theorem full_unary_admissible [Finite V] (C : Structure L V) {K : Class.{u,v} L}
    (hCompleted : CompletedClass K) (hK : C.IrreduciblesIn K) :
    C.FullUnaryAdmissible K := by
  intro x
  let D := C.singletonStructure x
  have hD : K D := C.singleton_mem_class hK x
  exact ⟨C.closureAt x,D,inferInstance,hD,hCompleted D hD,
    C.singleton_oneGenerated x,⟨DiagramIso.refl D⟩⟩

end CCO.UnarySupport.Structure
