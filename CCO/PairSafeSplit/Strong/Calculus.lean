import CCO.PairSafeSplit.Strong.FullClass
import CCO.StrongExact.SourceExactCalculus
import CCO.SAPPoint
import CCO.SAPEdge

/-! Actual new-source STRONG laws, after independent actual marked SAP.
No abstract sector algebra or uninstantiated source provider is assumed. -/

universe u v w t
namespace CCO.PairSafeSplit.Strong
open APCharacter RigidGroupoid.Geometry
open APCharacter.SourceAge.UnarySource
noncomputable section
variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable {H : HomogeneousSource S G} {C : ExactCalculus S} {r : ι} {A : Kernel S r}
variable (P : SourcePhase S H C A) (cco : SemanticCCO.{u,v,max u v,w} S)
variable (I : Identification S H (P.completion_property cco)) (sap : AgeSAP S)

include sap

/-- Strongly amalgamated actual input edges have a genuine diversity
output, also when any or all child sort labels repeat. -/
theorem forks : (source I).RealPointGluing :=
  (source I).realPointGluing_of_SAP (homogeneous I) (SAP.unary_source_sap P cco I sap)

theorem fork_menus {b c d : Rank.Child (β I)}
    {U : (source I).Menu b c} {V : (source I).Menu c d}
    (hU : U.Nonempty) (hV : V.Nonempty) : ((source I).product U V).Nonempty :=
  (source I).product_nonempty_of_point_gluing (forks P cco I sap) hU hV

theorem edge_gluing : (source I).RealEdgeGluing :=
  (source I).realEdgeGluing_of_SAP (homogeneous I) (SAP.unary_source_sap P cco I sap)

theorem associativity {a b c d : Rank.Child (β I)}
    (U : (source I).Menu a b) (V : (source I).Menu b c) (W : (source I).Menu c d) :
    (source I).product ((source I).product U V) W =
      (source I).product U ((source I).product V W) :=
  (source I).product_assoc_of_edge_gluing (edge_gluing P cco I sap) U V W

theorem set_pasch {a b c d : Rank.Child (β I)}
    (U : (source I).Menu a b) (V : (source I).Menu b c)
    (W : (source I).Menu a d) (Z : (source I).Menu d c)
    (h : ((source I).product U V ∩ (source I).product W Z).Nonempty) :
    ((source I).product ((source I).opposite U) W ∩
      (source I).product V ((source I).opposite Z)).Nonempty :=
  (source I).set_pasch_of_edge_gluing (edge_gluing P cco I sap) U V W Z h

omit sap in
theorem peirce {a b c : Rank.Child (β I)}
    (p : (source I).Atom a b) (q : (source I).Atom b c) (r : (source I).Atom a c) :
    (source I).Triangle p q r ↔ (source I).Triangle r ((source I).conv q) p :=
  (source I).triangle_peirce p q r

/-- Genuine finite positive STRONG 2-Helly, with the empty word family
included, on every ordered pair of current child sorts. -/
theorem word_helly : StrongExact.WordHelly (source I) :=
  StrongExact.wordHelly_of_SAP_CCO (source I) (homogeneous I)
    (SAP.unary_source_sap P cco I sap) (semanticCCO I)

end
end CCO.PairSafeSplit.Strong
