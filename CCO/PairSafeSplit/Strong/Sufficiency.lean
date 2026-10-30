import CCO.PairSafeSplit.Strong.Calculus
import CCO.PairSafeSplit.Strong.Primality

/-! Context-qualified phase sufficiency for the actual maximal-character
source. This packages proved source statements; its only SAP hypothesis is
original SAP, and no abstract three-property marked-subclass criterion is
asserted. -/

universe u v w t
namespace CCO.PairSafeSplit.Strong
open APCharacter RigidGroupoid.Geometry
open APCharacter.SourceAge.UnarySource
noncomputable section
variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable {H : HomogeneousSource S G} {C : ExactCalculus S} {r : ι} {A : Kernel S r}
variable (P : SourcePhase S H C A) (cco : SemanticCCO.{u,v,max u v,w} S)
variable (I : Identification S H (P.completion_property cco))

/-- Every clause refers to the SAME actual canonical child source or the
SAME original maximal-character instance. No arbitrary marked subclass,
new-source SAP provider, or word-normal-form provider is a premise. -/
structure ActualPhaseSufficiency : Prop where
  sourceSAP : AgeSAP (source I)
  sourceHomogeneous : HomogeneousSource (source I) (FullGroup I)
  sourceHOMCCO : SemanticCCO.{u,v,0,w} (source I)
  fullClass : ∀ {V : Type (max u v)} (D : CompleteDiagram (S := source I) V),
    FullTriangleLegal P cco I D ↔ ∃ f : DiagramHom D.diagram, f.IsInjective
  fullWord : ∀ {c d : Rank.Child (β I)} (p : PositiveWord (source I) c d)
    (x : Rank.Point (β I) (tag I) c) (z : Rank.Point (β I) (tag I) d),
    PositiveWord.represented (source I) p x z ↔
      PositiveWord.represented S (forgetWord I p) x.val z.val
  strongWord : ∀ {c d : Rank.Child (β I)} (p : PositiveWord (source I) c d),
    Subtype.val '' PositiveWord.profile (source I) p =
      {a | a ∈ PositiveWord.profile S (forgetWord I p) ∧ P.allows (some a) c.2.val d.2.val}
  realForks : (source I).RealPointGluing
  realEdgeGluing : (source I).RealEdgeGluing
  associative : ∀ {a b c d : Rank.Child (β I)}
    (U : (source I).Menu a b) (V : (source I).Menu b c) (W : (source I).Menu c d),
    (source I).product ((source I).product U V) W =
      (source I).product U ((source I).product V W)
  setPasch : ∀ {a b c d : Rank.Child (β I)}
    (U : (source I).Menu a b) (V : (source I).Menu b c)
    (W : (source I).Menu a d) (Z : (source I).Menu d c),
    ((source I).product U V ∩ (source I).product W Z).Nonempty →
    ((source I).product ((source I).opposite U) W ∩
      (source I).product V ((source I).opposite Z)).Nonempty
  typedPeirce : ∀ {a b c : Rank.Child (β I)}
    (p : (source I).Atom a b) (q : (source I).Atom b c) (r : (source I).Atom a c),
    (source I).Triangle p q r ↔ (source I).Triangle r ((source I).conv q) p
  profileTwoHelly : StrongExact.WordHelly (source I)
  strongPhasePrimality : ∀ (b c : Reached S A)
    (ps : List (PositiveWord S b.val c.val)) (δ : Bit),
    (StrongExact.present S ps).Nonempty →
    StrongExact.present S ps ⊆ sheetPalette P b c δ →
    ∃ p ∈ ps, PositiveWord.profile S p ⊆ sheetPalette P b c δ

theorem actual_phase_sufficiency (sap : AgeSAP S) : ActualPhaseSufficiency P cco I where
  sourceSAP := SAP.unary_source_sap P cco I sap
  sourceHomogeneous := homogeneous I
  sourceHOMCCO := semanticCCO I
  fullClass := full_lifted_triangle_class P cco I
  fullWord := represented_normal_form P cco I
  strongWord := profile_image_normal_form P cco I sap
  realForks := forks P cco I sap
  realEdgeGluing := edge_gluing P cco I sap
  associative := associativity P cco I sap
  setPasch := set_pasch P cco I sap
  typedPeirce := peirce P cco I
  profileTwoHelly := word_helly P cco I sap
  strongPhasePrimality := typed_epp P sap cco

end
end CCO.PairSafeSplit.Strong
