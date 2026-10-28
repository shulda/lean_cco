import CCO.StrongExact.PCExactness
import CCO.StrongExact.ExactEndpointSemantics
import CCO.StrongExact.TripleOccurrence
import CCO.StrongExact.PairSurvivorCompletion

/-!
# C13: the canonical nonempty PC family is exactly the original exact family

Forward exactness is the noncircular finite-iteration theorem. Conversely
C07 realizes every original exact menu as the full survivor menu of a
finite strong diagram, and the proved C12 selected-survivor theorem makes
it that diagram's canonical PC menu. The same conversion on C09's actual
three-root graph gives the full canonical three-menu iff-PC criterion.
The separate strict-simple-path formula is not assumed here.
-/

universe u v w z
namespace CCO.StrongPC
variable {ι : Type u} {X : ι → Type v}
variable {S : AtomicSource.{u,v,w} ι X} {V : Type z}
variable (D : PartialDiagram S V)

/-- The selected-survivor theorem applied to a genuinely strongly
completable diagram; every pair's zero-free premise is discharged. -/
theorem fixedNetwork_eq_survivor_of_strongCompletion
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,z,w} S) (hD : D.HasStrongCompletion)
    (x y : V) (hxy : x ≠ y) :
    fixedNetwork D ⟨x,y,hxy⟩ = D.survivor x y hxy := by
  obtain ⟨f,hf⟩ := hD
  exact fixedNetwork_eq_survivor D H sap cco
    (fixedNetwork_nonempty_of_completion D f hf) x y hxy

end CCO.StrongPC

namespace CCO.StrongExact
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {i j k : ι}

/-- An original-sort menu occurring as a canonical fixed PC domain of
an actual finite strongly completable private-word diagram. -/
def CanonicalThetaDomain (A : S.Menu i j) : Prop :=
  ∃ (ws : List (PositiveWord S i j)) (T : ThetaEdges S ws),
    T.toDiagram.HasStrongCompletion ∧
      StrongPC.fixedNetwork T.toDiagram
        ⟨thetaLeft S ws,thetaRight S ws,thetaLeft_ne_right S ws⟩ = A

/-- Every original nonempty exact menu is an ACTUAL canonical PC
menu, using the SAME graph that realizes all its endpoint atoms. -/
theorem canonicalThetaDomain_of_exact_of_SAP_CCO
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,0,w} S)
    {A : S.Menu i j} (hA : Exact S A) : CanonicalThetaDomain S A := by
  obtain ⟨ws,T,hCompletion,hSurvivor,_hWords⟩ :=
    exact_menu_survivor_representation_of_SAP S H sap hA
  have hFixed := StrongPC.fixedNetwork_eq_survivor_of_strongCompletion
    T.toDiagram H sap cco hCompletion
    (thetaLeft S ws) (thetaRight S ws) (thetaLeft_ne_right S ws)
  exact ⟨ws,T,hCompletion,hFixed.trans hSurvivor⟩

/-- A canonical domain of an actual strong diagram belongs to the
original exact family by finite evaluated PC-iteration closure. -/
theorem exact_of_canonicalThetaDomain_of_SAP_CCO
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,0,w} S)
    {A : S.Menu i j} (hA : CanonicalThetaDomain S A) : Exact S A := by
  obtain ⟨ws,T,hCompletion,hFixed⟩ := hA
  have hExact := StrongPC.fixedNetwork_exact_of_strongCompletion
    T.toDiagram H sap cco hCompletion
    ⟨thetaLeft S ws,thetaRight S ws,thetaLeft_ne_right S ws⟩
  rw [hFixed] at hExact
  exact hExact

/-- C13 family equality: the actual canonical nonempty PC domains are
precisely the ORIGINAL positive-word finite-meet exact menus. Forward
inclusion holds for arbitrary finite strong diagrams via PCExactness;
the converse supplies a concrete finite private-word witness. -/
theorem exact_iff_canonicalThetaDomain_of_SAP_CCO
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,0,w} S) {A : S.Menu i j} :
    Exact S A ↔ CanonicalThetaDomain S A :=
  ⟨canonicalThetaDomain_of_exact_of_SAP_CCO S H sap cco,
    exact_of_canonicalThetaDomain_of_SAP_CCO S H sap cco⟩

/-- Three menus occurring simultaneously as the ACTUAL canonical PC
menus on three distinct original-sort roots in one strong word diagram. -/
def ThreeRootCanonicalOccurrence
    (A : S.Menu i j) (B : S.Menu j k) (C : S.Menu i k) : Prop :=
  ∃ (W : TripleWords S i j k) (x : X i) (y : X j) (z : X k)
    (seed : TripleLiteralLines S W x y z),
    (tripleDiagram S W x y z seed).HasStrongCompletion ∧
    StrongPC.fixedNetwork (tripleDiagram S W x y z seed)
      ⟨.inl .left,.inl .middle,tripleSideRoots_ne S W .left⟩ = A ∧
    StrongPC.fixedNetwork (tripleDiagram S W x y z seed)
      ⟨.inl .middle,.inl .right,tripleSideRoots_ne S W .right⟩ = B ∧
    StrongPC.fixedNetwork (tripleDiagram S W x y z seed)
      ⟨.inl .left,.inl .right,tripleSideRoots_ne S W .across⟩ = C

/-- Necessity uses all three support inclusions of the ACTUAL
canonical stable network; no exactness or source provider is assumed. -/
theorem threeRootCanonicalOccurrence_PC
    {A : S.Menu i j} {B : S.Menu j k} {C : S.Menu i k}
    (h : ThreeRootCanonicalOccurrence S A B C) : S.PC A B C := by
  obtain ⟨W,x,y,z,seed,_hCompletion,hA,hB,hC⟩ := h
  have hPC := StrongPC.fixedNetwork_PC (tripleDiagram S W x y z seed)
    (x := .inl .left) (y := .inl .middle) (z := .inl .right)
    (tripleSideRoots_ne S W .left) (tripleSideRoots_ne S W .right)
    (tripleSideRoots_ne S W .across)
  rw [hA,hB,hC] at hPC
  exact hPC

/-- C09's same-graph full survivor domains are canonical PC domains
because its actual injective completion discharges every zero-free gate. -/
theorem threeRootCanonicalOccurrence_of_PC_of_SAP_CCO
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,0,w} S)
    {A : S.Menu i j} {B : S.Menu j k} {C : S.Menu i k}
    (hA : Exact S A) (hB : Exact S B) (hC : Exact S C)
    (hPC : S.PC A B C) : ThreeRootCanonicalOccurrence S A B C := by
  obtain ⟨W,x,y,z,seed,hCompletion,hLeft,hRight,hAcross⟩ :=
    threeRootWordOccurrence_of_PC_of_SAP S H sap hA hB hC hPC
  let D := tripleDiagram S W x y z seed
  have hFixed := StrongPC.fixedNetwork_eq_survivor_of_strongCompletion
    D H sap cco hCompletion
  exact ⟨W,x,y,z,seed,hCompletion,
    (hFixed (.inl .left) (.inl .middle) (tripleSideRoots_ne S W .left)).trans hLeft,
    (hFixed (.inl .middle) (.inl .right) (tripleSideRoots_ne S W .right)).trans hRight,
    (hFixed (.inl .left) (.inl .right) (tripleSideRoots_ne S W .across)).trans hAcross⟩

/-- Full C13 canonical three-root criterion, with arbitrary repeated
original named sorts, original exact menus and all three PC supports. -/
theorem threeRootCanonicalOccurrence_iff_PC_of_SAP_CCO
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,0,w} S)
    {A : S.Menu i j} {B : S.Menu j k} {C : S.Menu i k}
    (hA : Exact S A) (hB : Exact S B) (hC : Exact S C) :
    ThreeRootCanonicalOccurrence S A B C ↔ S.PC A B C :=
  ⟨threeRootCanonicalOccurrence_PC S,
    threeRootCanonicalOccurrence_of_PC_of_SAP_CCO S H sap cco hA hB hC⟩

end CCO.StrongExact
