import CCO.Examples
import CCO.StrongExact.FinitePC
import CCO.StrongExact.Survivors
import CCO.StrongExact.PathSupport

/-!
# Concrete STRONG PC regression: 0 -> 1 -> 0 and same-sort repetition

The three *formal* vertices are distinct, while the first and third
share a named sort. The actual witnesses carry distinct numerical
coordinates, so none of the STRONG products picks up fake identity.
The example source is only a finite-palette sanity test; we do not
claim the source to satisfy SAP or CCO.
-/

namespace CCO.StrongExact.Examples

private abbrev S := CCO.Examples.trivialPalette

/-- Three formal vertices with two named sorts: 0 and 2 have sort 0,
while 1 has sort 1. Every distinct pair displays the genuine Unit
diversity atom. -/
def toyDiagram : PartialDiagram S (Fin 3) where
  finite_type := inferInstance
  vertexSort := fun x => if x = 1 then 1 else 0
  edge := fun _ _ _ => some ()
  edge_reverse := by
    intro x y h a
    cases a
    rfl

/-- The actual realization x ↦ x.val preserves every displayed atom.
It is injective even though two different vertices have the same sort. -/
def toyCompletion : DiagramHom toyDiagram where
  point := fun x => x.val
  preserves_edge := by
    intro x y h a _
    cases a
    apply CCO.Examples.literal_diversity
    intro he
    exact h (Fin.ext he)

theorem toyCompletion_injective : toyCompletion.IsInjective := by
  intro x y he
  have hv := congrArg
    (fun p : Sigma (fun _ : Fin 2 => Nat) => p.2) he
  exact Fin.ext hv

/-- Every genuine old colour survives all Boolean PC iterations. -/
theorem toy_survives (n : Nat) (x y : Fin 3) (hxy : x ≠ y) :
    () ∈ StrongPC.iterate toyDiagram (StrongPC.initial toyDiagram) n
      ⟨x, y, hxy⟩ := by
  apply StrongPC.supports_all_iterates toyDiagram
    toyCompletion toyCompletion_injective n ⟨x, y, hxy⟩ ()
  exact CCO.Examples.literal_diversity (by
    intro he
    exact hxy (Fin.ext he))

/-- On the concrete cross-sort and same-sort triangle, all three full
survivor domains satisfy the literal all-coordinate PC condition. -/
example : S.PC
    (toyDiagram.survivor 0 1 (by decide))
    (toyDiagram.survivor 1 2 (by decide))
    (toyDiagram.survivor 0 2 (by decide)) :=
  toyDiagram.survivor_PC 0 1 2 (by decide) (by decide) (by decide)

/-- The finite canonical PC refinement is genuinely stable. -/
example : StrongPC.Stable toyDiagram (StrongPC.fixedNetwork toyDiagram) :=
  StrongPC.fixedNetwork_stable toyDiagram

/-- Concrete specified two-edge positive path 0→1→2, whose
first and last points have the SAME named sort while the internal
point has a different named sort. No true diagonal factor occurs. -/
def toyTwoEdgePath : StrongPC.SpecifiedPath toyDiagram 0 2 :=
  .cons (y := (1 : Fin 3)) (by decide) (by decide) () (by rfl)
    (.edge (by decide) () (by rfl))

/-- Genuine dependent-typed downstream C11 consumer, not just a
syntactically well-typed definition of an untested lemma. -/
theorem toy_two_edge_supported :
    StrongPC.fixedNetwork toyDiagram ⟨0, 2, by decide⟩ ⊆
      PositiveWord.profile S toyTwoEdgePath.word :=
  StrongPC.fixedNetwork_subset_path_profile toyDiagram toyTwoEdgePath

end CCO.StrongExact.Examples
