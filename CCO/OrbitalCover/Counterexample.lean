import CCO.OrbitalCover.Example.Model
import CCO.OrbitalCover.Example.Covers
import CCO.OrbitalCover.Example.APObstruction

/-! The actual nine-colour counterexample, its universal coarse-cover
obstruction, and the two simultaneous finer good unary refinements. -/
universe z
namespace CCO.OrbitalCover.Example
open ParityHasse.Original

/-- The full diagonal equivalence's actual diversity palette is exactly
the non-box palette computed in the independent STRONG profile proof. -/
theorem diagonal_actual_palette (x y : Point) :
    diagonalSetoid x y ↔ pattern x y ∈ diagonalPalette := by
  rw [diagonal_pattern]
  simp only [diagonalPalette,Set.mem_insert_iff,Set.mem_singleton_iff]
  constructor
  · rintro ⟨b,hb⟩
    rcases bit_cases b with rfl|rfl
    · exact .inl hb
    · exact .inr hb
  · rintro (h|h)
    · exact ⟨0,h⟩
    · exact ⟨1,h⟩

/-- C40, the source-level `prop:bad-diagonal-split` consumer. All source
properties and good-prefix properties are constructed, while the bad
orientation quantifier ranges over every actual unary predicate. -/
theorem bad_diagonal_split :
    Nat.card Colour=9 ∧ Countable Point ∧ Infinite Point ∧
    HomogeneousSource source Aut ∧ AgeSAP source ∧ SemanticCCO.{0,0,z,0} source ∧
    (∀ (V : Type z) (A : CompleteDiagram (S := source) V),
      A.SmallRealizable → ∃ f : DiagramHom A.diagram, f.IsInjective) ∧
    diagonal ⋖ coarse ∧
    (∀ a : Point, relativeIndex diagonal.val coarse.val a=2) ∧
    (∃ P : Point → Bit, Orientation P) ∧
    (∀ P : Point → Bit, Orientation P → ¬(markedModel P).AgeAP) ∧
    ownerEq ⋖ pEq ∧ ownerEq ⋖ qEq ∧
    (∀ k : Prefix.Stage, HomogeneousSource (Prefix.source k) (Prefix.FullGroup k) ∧
      AgeSAP (Prefix.source k) ∧ SemanticCCO.{0,0,z,0} (Prefix.source k)) := by
  exact ⟨actual_model.{z}.1,inferInstance,inferInstance,homogeneous,strongAmalgamation,
    semanticCCO,fun _ A => triangle_defined A,diagonal_cover,diagonal_index_two,
    ⟨fun x => x.p+x.q+(0:Bit),orientation_of_offset (fun _ _ => 0)⟩,
    fun _ hP => every_orientation_not_AP hP,p_cover,q_cover,Prefix.actual_prefix⟩

end CCO.OrbitalCover.Example
