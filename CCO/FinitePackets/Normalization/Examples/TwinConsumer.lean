import CCO.FinitePackets.Normalization.Examples.TwinQuotient
import CCO.StrongExact.TriangleFullness

/-! B014 C30–C31, with every infinite-source provider instantiated. -/
universe z
namespace CCO.FinitePackets.Normalization.Examples.Twin
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds

/-- Any complete diagram with its actual triangles, edges and vertices legal
embeds into this source. This is the actual triangle-defined age consumer. -/
theorem triangle_defined {V : Type z} (A : CompleteDiagram (S := source) V)
    (hsmall : A.SmallRealizable) : ∃ f : DiagramHom A.diagram, f.IsInjective :=
  A.triangleFullness_of_homogeneous_CCO homogeneous semanticCCO hsmall

/-- Thin F does NOT imply absence of a nonidentity finite full-RAW-exact
kernel, even in a genuine infinite homogeneous AP+semantic-CCO source. -/
theorem thin_not_exact_free_source :
    HomogeneousSource source Aut ∧ AgeAP source ∧ SemanticCCO.{0,0,z,0} source ∧
    Nat.card Colour = 4 ∧ finitePacket source homogeneous = packetEq ∧
    (∀ x : Point, Nat.card (ClassPoint source () packetEq x) = 2) ∧
    (∀ a : Colour, (∃ x y, packetEq x y ∧ colour x y = some a) →
      ∀ x, ∃! y, colour x y = some a) ∧
    ExactCRT.IsExactEq source (i := ()) packetEq.val ∧ packetEq ≠ ⊥ ∧
    Geometry.MinimalInfiniteCut source rowEq ∧
    (∀ x r, r ≠ row x →
      Nat.card {y : Point // row y = r ∧ colour x y = some Colour.column} = 2) ∧
    Nat.card ActualCellAtom = 3 ∧ Nat.card ActualCellAtom < Nat.card Colour := by
  refine ⟨homogeneous,ageAP,semanticCCO,?_,finitePacket_eq,packet_card,
    all_packet_atoms_thin,packet_exact,packet_nonidentity,row_minimal_infinite,
    conditional_fibre_card,quotient_diversity_card,quotient_palette_strictly_decreases⟩
  exact Nat.card_eq_fintype_card.trans colour_card

end CCO.FinitePackets.Normalization.Examples.Twin
