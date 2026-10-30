import CCO.RelationalCompletion.Atomic.Cycle

/-! The standalone AP plus semantic homomorphic CCO triangle-fullness theorem.
It assumes neither SAP, ambient realization, finite palette, homogeneous limit,
functions, collision unfolding, nor an already triangle-full class. -/
universe u v
namespace CCO.RelationalCompletion.Atomic
variable {P : Palette.{u,v}}

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
