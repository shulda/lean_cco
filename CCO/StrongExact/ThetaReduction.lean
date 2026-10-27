import CCO.StrongExact.DirectBranches
import CCO.StrongExact.PrescribedPathWitness
import CCO.StrongExact.CycleCompletion

/-!
# C07 source-level reduction to one explicit theta graph obligation

This file does NOT assume or assert the missing theta 2-Helly theorem.
Instead it isolates the exact finite graph geometry needed to derive it
from the ACCEPTED semantic homomorphic CCO and genuine SAP
injectivization.

A theta provider must construct an actual typed partial diagram over
the already-defined finite shared-root/private-vertex type, show
that EVERY specified simple cycle has a homomorphism, and show
that every actual diagram homomorphism represents EVERY positive
branch word between the two literal formal roots. No real or
formal roots are assumed injective in the original homomorphism.

The consequent 2-Helly theorem is deliberately CONDITIONAL on this
concrete diagram-construction property until the private-branch
edge/cycle classification is compiled. This is not a new axiom,
not a disguised provider, and not an unconditional source C07 claim.
-/

universe u v w

namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {i j : ι}

/-- An ACTUAL finite typed partially specified graph on the private
theta vertices. The named sort function is fixed by the word paths;
only its old diversity edges and their legal converses are data. -/
structure ThetaEdges (ws : List (PositiveWord S i j)) where
  edge : ∀ (x y : thetaVertices S ws), x ≠ y →
    Option (S.Atom
      (thetaVertexSort S ws x) (thetaVertexSort S ws y))
  edge_reverse : ∀ (x y : thetaVertices S ws) (h : x ≠ y)
      (a : S.Atom
        (thetaVertexSort S ws x) (thetaVertexSort S ws y)),
    edge x y h = some a ↔
      edge y x h.symm = some (S.conv a)

/-- The actual B001 partial-diagram API, with literal finite vertex
and named-sort functions. All CCO checks apply without coercing
an equality step to a diversity atom. -/
def ThetaEdges.toDiagram {ws : List (PositiveWord S i j)}
    (T : ThetaEdges S ws) :
    PartialDiagram S (thetaVertices S ws) where
  finite_type := finite_thetaVertices S ws
  vertexSort := thetaVertexSort S ws
  edge := T.edge
  edge_reverse := T.edge_reverse

/-- A theta edge construction represents ALL its displayed word
constraints over the SAME two original root points, even if its
homomorphism identifies private vertices. The pair of root points
will only be forced distinct after accepted SAP injectivization. -/
def ThetaEdges.RepresentsWords {ws : List (PositiveWord S i j)}
    (T : ThetaEdges S ws) : Prop :=
  ∀ (f : DiagramHom (T.toDiagram))
    (word : PositiveWord S i j), word ∈ ws →
    PositiveWord.represented S word
      (f.point (thetaLeft S ws)) (f.point (thetaRight S ws))

/-- Exactly the outstanding geometric C07 obligation. Every
pairwise-intersecting finite typed list must have ONE actual theta
diagram satisfying the old-cycle criterion and literal branch
representation. This is a quantified PROP, not a theorem or axiom. -/
def ThetaProvider : Prop :=
  ∀ {i j : ι} (ws : List (PositiveWord S i j)),
    PairwiseWordProfiles S ws →
      ∃ T : ThetaEdges S ws,
        (∀ C : SimpleCycle (T.toDiagram), CycleHom C) ∧
          T.RepresentsWords

/-- The accepted C06 injectivization/CCO theorem genuinely reduces
C07 2-Helly to the explicitly visible theta graph provider.
The final witnesses are actual ORIGINAL diversity atoms, not RAW
identity outputs and not a conditional transitive theorem hidden as
an unconditional source instance. -/
theorem wordHelly_of_thetaProvider
    {G : Type*} [Group G] [∀ q : ι, MulAction G (X q)]
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,0,w} S)
    (provider : ThetaProvider S) :
    WordHelly S := by
  intro i j ws hPair
  obtain ⟨T, hCycles, hWords⟩ := provider ws hPair
  have hStrong : (T.toDiagram).HasStrongCompletion :=
    (PartialDiagram.strongCompletion_iff_cycles_of_SAP_CCO
      H sap cco (T.toDiagram)).2 hCycles
  obtain ⟨f, hf⟩ := hStrong
  have hRootNe : f.image (thetaLeft S ws) ≠
      f.image (thetaRight S ws) := by
    intro he
    exact (thetaLeft_ne_right S ws) (hf he)
  obtain ⟨a, ha⟩ := S.some_colour_of_ne
    (f.point (thetaLeft S ws)) (f.point (thetaRight S ws))
    hRootNe
  refine ⟨a, ?_⟩
  intro word hw
  have hReal := hWords f word hw
  exact (positive_profile_iff_represented S H sap word a).2
    ⟨f.point (thetaLeft S ws),
      f.point (thetaRight S ws), hReal, ha⟩


/-- The HARD theta construction can restrict attention to words
of length at least two. When a direct one-letter branch occurs, C07
is already solved by the elementary singleton argument, so one need
not construct a parallel root-to-root edge or an artificial 2-cycle. -/
def LongThetaProvider : Prop :=
  ∀ {i j : ι} (ws : List (PositiveWord S i j)),
    PairwiseWordProfiles S ws →
    (∀ a : S.Atom i j,
      (PositiveWord.single a : PositiveWord S i j) ∉ ws) →
      ∃ T : ThetaEdges S ws,
        (∀ C : SimpleCycle (T.toDiagram), CycleHom C) ∧
          T.RepresentsWords

/-- Source C07 reduces to a theta construction only for the LONG
positive branches. The direct-edge case is proved independently
without semantic CCO or SAP. -/
theorem wordHelly_of_longThetaProvider
    {G : Type*} [Group G] [∀ q : ι, MulAction G (X q)]
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,0,w} S)
    (provider : LongThetaProvider S) :
    WordHelly S := by
  intro i j ws hPair
  by_cases hDirect : ∃ a : S.Atom i j,
      (PositiveWord.single a : PositiveWord S i j) ∈ ws
  · obtain ⟨a, ha⟩ := hDirect
    exact wordHelly_of_direct_branch S ws hPair a ha
  · have hLong : ∀ a : S.Atom i j,
        (PositiveWord.single a : PositiveWord S i j) ∉ ws := by
      intro a ha
      exact hDirect ⟨a, ha⟩
    obtain ⟨T, hCycles, hWords⟩ := provider ws hPair hLong
    have hStrong : (T.toDiagram).HasStrongCompletion :=
      (PartialDiagram.strongCompletion_iff_cycles_of_SAP_CCO
        H sap cco (T.toDiagram)).2 hCycles
    obtain ⟨f, hf⟩ := hStrong
    have hRootNe : f.image (thetaLeft S ws) ≠
        f.image (thetaRight S ws) := by
      intro he
      exact (thetaLeft_ne_right S ws) (hf he)
    obtain ⟨a, ha⟩ := S.some_colour_of_ne
      (f.point (thetaLeft S ws)) (f.point (thetaRight S ws))
      hRootNe
    refine ⟨a, ?_⟩
    intro word hw
    exact (positive_profile_iff_represented S H sap word a).2
      ⟨f.point (thetaLeft S ws),
        f.point (thetaRight S ws), hWords f word hw, ha⟩

end CCO.StrongExact
