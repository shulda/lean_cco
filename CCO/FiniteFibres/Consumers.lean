import CCO.FiniteFibres.Hasse
import CCO.FiniteFibres.RealExport
import CCO.FiniteFibres.SmallTargets
import CCO.FiniteFibres.Boundaries.Consumers

/-! Independent receiving uses of all four selected B042 source exports.
The finite target branches have no homogeneous/transitive source premise;
the relative-cover branch adds ONLY its actual full-group transitivity.
The actual finite fibre has the reduced occurring old palette. -/
universe v w t
namespace CCO.FiniteFibres

theorem finite_target_consumer {C : Type*} (T : Target C) (cco : SemanticCCO T) :
    (∀ a : C,(atomGraph T a).IsBipartite) ∧
      T.size ≤ 2 ^ Nat.card (Occurring T) ∧ ∃ k : Nat,Nat.card (Aut T) = 2^k :=
  ⟨atom_bipartite T cco,cardinal_le_bits T cco,automorphism_two_group T cco⟩

theorem finite_cover_consumer {C : Type*} (T : Target C) (cco : SemanticCCO T)
    (trans : ∀ x y : Fin T.size,∃ g : Aut T,g • x = y)
    (a : Fin T.size) (U V : Group.Correspondence.InvEq (Aut T) (Fin T.size)) (h : U ⋖ V) :
    Nat.card (Group.Correspondence.RelativeClass U V h.le a) = 2 :=
  finite_hasse_index_two T cco trans a h

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M)) [DecidableEq M]
variable {G : Type t} [Group G] [MulAction G M]
variable (H : HomogeneousSource S G) (cco : CCO.SemanticCCO.{0,v,0,w} S)
include H cco

/-- The actual inherited fibre's chosen FULL invariant chain has exactly
the stated cardinal and consumes at most the old original palette. -/
theorem actual_fibre_chain_consumer (A : Finset M)
    (q : ↥A → RealHull.Geometry.Atom S)
    [Nonempty (RealHull.Geometry.FibreSet S A q)] [Finite (RealHull.Geometry.FibreSet S A q)] :
    ∃ m : Nat,Nat.card (RealHull.Geometry.FibreSet S A q) = 2^m ∧
      m ≤ Nat.card (S.Atom () ()) := by
  let T := RealHull.Geometry.fibreSource S A q
  have h := actual_source_chain_bounds T
    (RealHull.Geometry.fibre_homogeneous S A q H)
    (RealHull.Geometry.fibre_semanticCCO S A q H cco)
  exact ⟨(sourceSaturatedChain T).length,h.1,
    h.2.trans (Real.fibre_palette_card_le S A q)⟩

/-- Nonempty actual real bases receive the literal requested quantitative
bound, with no additional finite-fibre provider in the assumptions. -/
theorem real_bound_consumer (A : Finset M) (hA : A.Nonempty) :
    (Real.acl S A).Finite ∧ Nat.card ↥(Real.acl S A) ≤
      A.card + (Nat.card (S.Atom () ())) ^ A.card * 2 ^ Nat.card (S.Atom () ()) := by
  have h := actual_real_fibre_bounds S H cco A
  exact ⟨h.2.1,h.2.2.1 hA⟩

/-- Infinite transitive empty-base algebraicity is handled separately. -/
theorem empty_infinite_consumer [Infinite M] : Real.acl S ∅ = ∅ :=
  (actual_real_fibre_bounds S H cco ∅).2.2.2.1

end CCO.FiniteFibres
