import CCO.FinitePackets.Normalization.ThinConsumers
import CCO.FinitePackets.Normalization.DescentChain
import CCO.FinitePackets.Normalization.QuotientThin
import CCO.FinitePackets.Normalization.SquarePowers

/-! Complete source-level consumers: a genuine normalization chain ends
with the actual regular translation group, and the twin source must take
a nonzero step despite its trivial square regularizer. -/
universe v w t
namespace CCO.FinitePackets.Normalization
open CCO.ParityHasse.Original CCO.RealHull.Geometry
variable {G : Type t} [Group G]

theorem SourceNode.normalization_with_regular_group (N : SourceNode.{v,t} G) :
    ∃ T : SourceNode.{v,t} G, ∃ n : Nat, ∃ chain : SourceNode.Chain N T n,
      Function.Surjective chain.projection ∧ NoFiniteExactKernel T.source ∧
      ∃ d : Nat, Nonempty (Translation T.source (Geometry.sigma T.source T.homogeneous ⊥) G ≃*
        Multiplicative (Fin d → ZMod 2)) ∧
      Nat.card (Translation T.source (Geometry.sigma T.source T.homogeneous ⊥) G) = 2^d ∧
      n ≤ N.palette := by
  obtain ⟨T,n,⟨chain⟩,ht,hthin,hlen⟩ := N.finite_normalization_thin
  obtain ⟨d,he,hcard⟩ := translation_elementary_abelian T.source
    (Geometry.sigma T.source T.homogeneous ⊥) T.homogeneous hthin
  exact ⟨T,n,chain,chain.projection_surjective,ht,d,he,hcard,hlen⟩

namespace Examples.Twin

/-- The very packet ignored by the square regularizer is a legal FIRST
actual source-preserving normalization kernel. -/
noncomputable def twinFiniteExactKernel : FiniteExactKernel source where
  kernel := packetEq
  finite := (Geometry.finiteIndex_bottom_iff_finite_classes source packetEq).mpr packet_finite
  exact := ExactCRT.exactPresentation source packet_exact
  represents := ExactCRT.exactPresentation_represents source packet_exact
  proper := packet_nonidentity

theorem actual_normalization_requires_step :
    ∃ K : FiniteExactKernel source, ∃ T : SourceNode.{0,0} Aut, ∃ n : Nat,
      Nonempty (SourceNode.Chain (quotientNode source homogeneous semanticCCO K) T n) ∧
      NoFiniteExactKernel T.source ∧
      ThinBottom T.source (Geometry.sigma T.source T.homogeneous ⊥) ∧ n+1 ≤ 4 := by
  obtain hterm | ⟨K,T,n,hchain,ht,hthin,hlen⟩ :=
    finite_exact_normalization_thin source homogeneous semanticCCO
  · exact False.elim (regularizer_stops_but_exact_normalization_does_not.2 hterm.1)
  · refine ⟨K,T,n,hchain,ht,hthin,?_⟩
    letI := source.finiteAtom () ()
    have hc : Nat.card (source.Atom () ()) = 4 :=
      Nat.card_eq_fintype_card.trans colour_card
    simpa only [hc] using hlen

end Examples.Twin
end CCO.FinitePackets.Normalization
