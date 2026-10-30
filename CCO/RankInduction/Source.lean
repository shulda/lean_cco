import CCO.RankInduction.Constructor
import CCO.RankInduction.GlobalPhases
import CCO.RankInduction.AbsoluteWitness
import CCO.RankInduction.Transitivity
import CCO.RankInduction.StandingSource

/-! Five source exports: the conditional P rank construction, elementary
full palette, globally discharged rooted and ordinary EPPA, and the SAME
closed vertex-transitive witness. No Lower, LowerClosed, owner master,
factor stage or HKN provider remains a premise of the global results.
The human article's source-relative candidate scope is retained; no
coherent extension assignment is asserted. -/

universe v w t
namespace CCO.RankInduction
noncomputable section
open RawExact Owners.Product Owners.Provider FinitePackets.Normalization

variable {G : Type t} [Group G]

/-- The ENTIRE conjunction is proved for EVERY source at EVERY rank,
not merely the rooted projection for one original input. -/
theorem all_sources_complete : ∀ N : SourceNode.{v,t} G, PhaseComplete N := by
  intro N
  exact phased_induction
    (fun X : SourceNode.{v,t} G => closed_rank_constructor X.source X.homogeneous X.cycles)
    (rank N.source) N rfl

variable {M : Type v} [MulAction G M] [Countable M]
variable (S : AtomicSource.{0,v,w} Unit (fun _ => M)) (H : HomogeneousSource S G)
variable (cco : SemanticCCO.{0,v,v,w} S)

/-- Arbitrary name universe: actual quotients belong to the completed
universal family before their lower conclusions are used here. -/
theorem source_complete :
    ClosedRooted S G ∧ OrdinaryEPPA G M ∧ MasterProperty S G H cco := by
  have complete : ∀ N : SourceNode.{v,t} G, PhaseComplete N := all_sources_complete
  have pcl := closed_rank_constructor S H cco
    (universal_lower S H cco complete) (universal_lower_closed S H cco complete)
  have ordinary := ordinary_from_rooted S H (ClosedRooted.rooted _ G pcl)
  refine ⟨pcl,ordinary,?_⟩
  intro A0 finiteA nonemptyA
  exact Owners.Master.actual_owner_master S H cco A0 finiteA nonemptyA
    (universal_all_quotients S H cco complete)

/-- `lem:acf-rank-step`: plain Lower ONLY. Absolute closure is the target;
the chosen witness is not asserted closed by this original rank lemma. -/
theorem rank_relative_rooted (lower : Lower S G H cco)
    (safe : Set (S.Atom () ()))
    (hs : FiniteLift.StrongClosedAmalgamation (FiniteLift.FullAut G M)
      (FiniteLift.aclSet (FiniteLift.FullAut G M)) (S.menuRel safe))
    (A0 : Set M) (finiteA : A0.Finite) (nonemptyA : A0.Nonempty) :
    ∃ W : Set M, AbsoluteWitness (G := G) S safe A0 W := by
  obtain ⟨W,hW⟩ := rank_relative_constructor S H cco lower safe
    (strong_closed_from_full S H _ hs) A0 finiteA nonemptyA
  exact ⟨W,witness_absolute S H safe A0 W finiteA hW⟩

include H in
omit [Countable M] in
/-- `lem:acf-full-palette`: elementary closed strong amalgamation under
FULL original automorphisms. No CCO or EPPA hypothesis is consumed. -/
theorem full_palette :
    FiniteLift.StrongClosedAmalgamation (FiniteLift.FullAut G M)
      (FiniteLift.aclSet (FiniteLift.FullAut G M)) (S.menuRel (i := ()) (j := ()) Set.univ) :=
  strong_closed_to_full S H _ (full_palette_strong_closed_amalgamation S H)

include H cco in
/-- `thm:main-rooted-acf`: all lower schemas have been discharged by
the actual global construction; all maps act on one finite original W. -/
theorem rooted_acf (safe : Set (S.Atom () ()))
    (hs : FiniteLift.StrongClosedAmalgamation (FiniteLift.FullAut G M)
      (FiniteLift.aclSet (FiniteLift.FullAut G M)) (S.menuRel safe))
    (A0 : Set M) (finiteA : A0.Finite) (nonemptyA : A0.Nonempty) :
    ∃ W : Set M, AbsoluteWitness (G := G) S safe A0 W := by
  obtain ⟨W,hW,-⟩ := (source_complete S H cco).1 safe
    (strong_closed_from_full S H _ hs) A0 finiteA nonemptyA
  exact ⟨W,witness_absolute S H safe A0 W finiteA hW⟩

include H cco in
/-- `thm:main-ordinary-eppa`, including its own empty-input convention. -/
theorem ordinary_eppa : OrdinaryEPPA G M := (source_complete S H cco).2.1

include H cco in
/-- `cor:acf-closed-transitive`: construct the closed rooted witness
FIRST, then derive transitivity of that SAME actual original carrier. -/
theorem closed_transitive_witness (safe : Set (S.Atom () ()))
    (hs : FiniteLift.StrongClosedAmalgamation (FiniteLift.FullAut G M)
      (FiniteLift.aclSet (FiniteLift.FullAut G M)) (S.menuRel safe))
    (A0 : Set M) (finiteA : A0.Finite) (nonemptyA : A0.Nonempty) :
    ∃ W : Set M, AbsoluteWitness (G := G) S safe A0 W ∧
      FiniteLift.aclSet (FiniteLift.FullAut G M) W = W ∧ VertexTransitive (G := G) W := by
  obtain ⟨W,hW,hclosed⟩ := (source_complete S H cco).1 safe
    (strong_closed_from_full S H _ hs) A0 finiteA nonemptyA
  exact ⟨W,witness_absolute S H safe A0 W finiteA hW,
    closed_absolute S H W hW.finite hclosed,witness_vertex_transitive S H safe A0 W hW⟩

end
end CCO.RankInduction
