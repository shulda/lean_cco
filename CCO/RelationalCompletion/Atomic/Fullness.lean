import CCO.RelationalCompletion.Atomic.Cycle

/-! The standalone AP plus semantic homomorphic CCO triangle-fullness theorem.
It assumes neither SAP, ambient realization, finite palette, homogeneous limit,
functions, collision unfolding, nor an already triangle-full class. -/
universe u v
namespace CCO.RelationalCompletion.Atomic
variable {P : Palette.{u,v}}

/-- C25: completeness alone forces an arbitrary positive map to be injective. -/
theorem Hom.injective {A B : Model P} (f : Hom A.diagram B) :
    Function.Injective f.vertex := f.toEmbedding.vertex.injective

/-- C26: every target atom reflects, not merely the originally displayed one. -/
theorem Hom.atom_iff {A B : Model P} (f : Hom A.diagram B)
    (x y : Fin A.size) (a : P.Atom) :
    B.edge (f.vertex x) (f.vertex y) = some a ↔ A.edge x y = some a := by
  have h := f.toEmbedding.edge_eq x y
  change B.edge (f.vertex x) (f.vertex y) = A.edge x y at h
  rw [h]

/-- C26: complete unary tags reflect as well as being preserved. -/
theorem Hom.tag_iff {A B : Model P} (f : Hom A.diagram B)
    (x : Fin A.size) (t : P.Sorts) : B.tag (f.vertex x) = t ↔ A.tag x = t := by
  rw [f.tag_eq]

/-- C24–C29: complete input gives reflection after locally allowed semantic CCO. -/
theorem triangleFullness (K : Model P → Prop) (hereditary : Hereditary K)
    (ap : AP K) (cco : SemanticCCO K) (A : Model P) (small : SmallSubmodels K A) : K A := by
  obtain ⟨B, hKB, ⟨f⟩⟩ := cco A.diagram (localAllowed_of_small K A small)
    (cycleHomInto_of_AP K A ap small)
  exact hereditary ⟨f.toEmbedding⟩ hKB

/-- C28 includes the input itself, also for empty, singleton and two-point cases. -/
theorem small_input_mem (K : Model P → Prop) (A : Model P)
    (small : SmallSubmodels K A) (hsize : A.size ≤ 3) : K A := by
  have heq : A.pullback (Function.Embedding.refl (Fin A.size)) = A := by
    cases A
    rfl
  simpa only [heq] using small (Function.Embedding.refl (Fin A.size)) hsize

end CCO.RelationalCompletion.Atomic
