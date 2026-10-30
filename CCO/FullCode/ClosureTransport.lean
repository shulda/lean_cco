import CCO.FullCode.StructureTransport

/-! Exact old/expanded closure comparisons and actual image closure. -/

universe u v w
namespace CCO.FullCode.Structure
variable {L L₀ L₁ : Language.{u}} {V : Type v} {W : Type w}

theorem isClosed_reduct (C : Structure L₁ V) (ρ : Reduct L₀ L₁)
    {S : Set V} (hS : C.IsClosed S) : (C.reduct ρ).IsClosed S :=
  fun F x hx => hS (ρ.funcMap F) x hx

theorem closure_reduct_subset (C : Structure L₁ V) (ρ : Reduct L₀ L₁)
    (S : Set V) : (C.reduct ρ).closure S ⊆ C.closure S :=
  (C.reduct ρ).closure_minimal
    (C.isClosed_reduct ρ (C.isClosed_closure S)) (C.subset_closure S)

/-- In an expansion adding only relations, the named functions still cover
all functions; old and expanded unary generation then coincide automatically. -/
theorem closure_reduct_eq_of_surjective_funcMap (C : Structure L₁ V)
    (ρ : Reduct L₀ L₁) (hfunc : Function.Surjective ρ.funcMap) (S : Set V) :
    (C.reduct ρ).closure S = C.closure S := by
  apply Set.Subset.antisymm (C.closure_reduct_subset ρ S)
  apply C.closure_minimal ?_ ((C.reduct ρ).subset_closure S)
  intro F x hx y hy
  obtain ⟨F₀, rfl⟩ := hfunc F
  exact (C.reduct ρ).isClosed_closure S F₀ x hx hy

/-- The explicit support/reduct commutation equation, unlike finite term
normal forms, gives actual closure under every added expanded function. -/
theorem expanded_closed_of_support_reduct_commutes (C : Structure L₁ V)
    (ρ : Reduct L₀ L₁) (S : Set V)
    (commutes : C.closure S = (C.reduct ρ).closure S) :
    C.IsClosed ((C.reduct ρ).closure S) := by
  rw [← commutes]
  exact C.isClosed_closure S

theorem Embedding.image_closed {C : Structure L V} {D : Structure L W}
    (f : Embedding C D) {S : Set V} (hS : C.IsClosed S) :
    D.IsClosed (f.point '' S) := by
  rintro F _ ⟨x, hx, rfl⟩ y hy
  obtain ⟨z, hz, rfl⟩ := f.reflect_func F x y hy
  exact ⟨z, hS F x hx hz, rfl⟩

theorem Embedding.closure_image {C : Structure L V} {D : Structure L W}
    (f : Embedding C D) (S : Set V) :
    D.closure (f.point '' S) = f.point '' C.closure S := by
  apply Set.Subset.antisymm
  · apply D.closure_minimal (f.image_closed (C.isClosed_closure S))
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, C.subset_closure S hx, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    apply C.closure_minimal (S := S)
      (T := {x | f.point x ∈ D.closure (f.point '' S)}) ?_ ?_ hx
    · intro F x hx y hy
      exact D.isClosed_closure (f.point '' S) F (f.point x) hx
        (f.map_func F x y hy)
    · intro x hx
      exact D.subset_closure (f.point '' S) ⟨x, hx, rfl⟩

/-- This is C51's actual closure implication once old root generation and
the marked reduct-commutation equation are established for the chosen code
subset.  It applies to an arbitrary competing expanded host. -/
theorem image_expanded_closed_of_support_reduct_commutes
    (C : Structure L₁ W) (ρ : Reduct L₀ L₁)
    (D : Structure L₀ V) (j : Embedding D (C.reduct ρ))
    (roots : Set V) (generated : D.closure roots = Set.univ)
    (commutes : C.closure (j.point '' roots) =
      (C.reduct ρ).closure (j.point '' roots)) :
    C.IsClosed (Set.range j.point) := by
  have heq : (C.reduct ρ).closure (j.point '' roots) = Set.range j.point := by
    rw [j.closure_image, generated, Set.image_univ]
  rw [← heq]
  exact C.expanded_closed_of_support_reduct_commutes ρ _ commutes

theorem closure_induce_image (C : Structure L V) (S : Set V) (hS : C.IsClosed S)
    (A : Set S) :
    C.closure (Subtype.val '' A) = Subtype.val '' (C.induce S hS).closure A :=
  (C.inclusion S hS).closure_image A

end CCO.FullCode.Structure
