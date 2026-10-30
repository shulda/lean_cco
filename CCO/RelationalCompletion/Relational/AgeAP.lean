import CCO.RelationalCompletion.Relational.Homogeneous
import Mathlib.Data.Set.Finite.Range

universe u v
namespace CCO.RelationalCompletion.Relational.Structure
variable {L : Language.{u}} {W : Type v}

/-- The age of an actual homogeneous structure has ordinary AP. The finite
host is the FULL induced union of two aligned copies; their intersection
may exceed the root. This does not assume or prove strong amalgamation. -/
theorem Homogeneous.ageAP {U : Structure L W} (hom : U.Homogeneous) : U.AgeAP := by
  intro V₀ V₁ V₂ _ _ _ A B C _ hB hC s t
  obtain ⟨b⟩ := hB
  obtain ⟨c⟩ := hC
  obtain ⟨a, ha⟩ := hom V₀ A (b.comp s) (c.comp t)
  let p := a.toEmbedding.comp b
  let S : Set W := Set.range p.point ∪ Set.range c.point
  have hS : S.Finite := (Set.finite_range p.point).union (Set.finite_range c.point)
  let : Finite S := hS.to_subtype
  let l : Embedding B (U.induce S) := {
    point x := ⟨p.point x, Or.inl ⟨x, rfl⟩⟩
    injective := fun _ _ h => p.injective (congrArg Subtype.val h)
    rel_iff := fun R xs => p.rel_iff R xs }
  let r : Embedding C (U.induce S) := {
    point x := ⟨c.point x, Or.inr ⟨x, rfl⟩⟩
    injective := fun _ _ h => c.injective (congrArg Subtype.val h)
    rel_iff := fun R xs => c.rel_iff R xs }
  refine ⟨S, inferInstance, U.induce S, U.induced_mem_age S, l, r, ?_⟩
  intro x
  exact Subtype.ext (ha x)

end CCO.RelationalCompletion.Relational.Structure
