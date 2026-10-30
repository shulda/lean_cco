import CCO.RankInduction.FactorPremises
import CCO.RankInduction.RelativeWitnessReadout

/-! Every component of the normalized source stage is now constructed
from the actual B028 witness, with its native original finite owner
projection. No conditional component/provider is left as a headline input. -/

universe v w t
namespace CCO.RankInduction.Factors
noncomputable section
open RawExact ExactCRT CanonicalQuotients Owners.Product Owners.Provider Owners.Master
open MIGeometry ParityHasse.Original FinitePackets.Normalization RealClosure.Bounds AclOwners RelativeMI

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] [Countable M] [DecidableEq M]
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,v,w} S)
variable (normalized : NoFiniteExactKernel S) (A0 : Finset M)
variable (B : LowerMaster S H cco normalized (↑A0 : Set M)) (D : Direction S)
local instance componentConstructionCoreAction : MulAction G (Quotient (factorCore S H cco D).val) :=
  originalQuotientAction S H (hat S H (semanticCCO_change_universe S cco) D)
local instance componentConstructionOwnerInvariant : Invariant G (factorOwner S H cco normalized D).val :=
  exactInvariant S H cco (factorOwner S H cco normalized D)
local instance componentConstructionJointInvariant : Invariant G (jointKernel S H cco normalized).val :=
  exactInvariant S H cco (jointKernel S H cco normalized)

/-- C18/C19 are on the SAME fixed actual factor and its ENTIRE native
owner image. Every field is supplied by an actual proved construction. -/
theorem exists_component (lower : Lower S G H cco)
    (safe : Set (S.Atom () ()))
    (hs : FiniteLift.StrongClosedAmalgamation G (FiniteLift.aclSet G) (S.menuRel safe))
    (nonemptyA : A0.Nonempty) :
    Nonempty (Component S H cco normalized (↑A0 : Set M) safe B D) := by
  classical
  letI : Infinite (Quotient (factorCore S H cco D).val) :=
    factor_infinite S H (semanticCCO_change_universe S cco) normalized D
  let T := factorSource S H (semanticCCO_change_universe S cco) D
  let HT := factorH S H (semanticCCO_change_universe S cco) D
  let J := coarseCut S H (semanticCCO_change_universe S cco) normalized D
  let A := factorSeed S H cco A0 D
  let C := coarseOwners S H cco normalized A0 B D
  let overA := seed_over_coarse S H cco normalized A0 B D
  let e := coarseEquiv S H (semanticCCO_change_universe S cco) normalized D
  let E := coarseOwnerEquiv S H cco normalized A0 B D
  let he := coarseEquiv_equivariant S H (semanticCCO_change_universe S cco) normalized D
  let hE := coarseOwnerEquiv_val S H cco normalized A0 B D
  letI := originalQuotientAction T HT J
  obtain ⟨W⟩ := factor_witness S H cco normalized A0 B D lower safe hs nonemptyA
  have readout := relative_plain_closed T HT J A C overA W
    (semanticCCO_change_universe T (factorCCO S H (semanticCCO_change_universe S cco) D))
    (factor_normalized S H (semanticCCO_change_universe S cco) normalized D)
    (factorDirection S H (semanticCCO_change_universe S cco) normalized D)
    (factorDirection_unique S H (semanticCCO_change_universe S cco) normalized D)
    (coarse_eppa S H cco normalized A0 B D)
  let over := NativeTransport.over T HT J A C overA W e
    (factorOwners S H cco normalized B D) E hE
  let onto := NativeTransport.onto T HT J A C overA W e
    (factorOwners S H cco normalized B D) E hE
  refine ⟨{
    carrier := W.carrier
    ordinary := ?_
    closed := readout.2
    over := over
    onto := onto
    prescribed := ?_
    points := ?_ }⟩
  · exact (factorSeed_coe S H cco A0 D) ▸ readout.1
  · rw [← factorSeed_coe S H cco A0 D]
    exact NativeTransport.prescribed T HT J A C overA W e he
      (factorOwners S H cco normalized B D) E hE
  · exact NativeTransport.points T HT J A C overA W e he
      (factorOwners S H cco normalized B D) E hE

/-- Fix ONE strict lower joint master first; only then choose the actual
finite factors. All future original requests use this same stage. -/
theorem exists_source_stage (lower : Lower S G H cco)
    (normalized : NoFiniteExactKernel S) (many : 2 ≤ directionCount S)
    (safe : Set (S.Atom () ()))
    (hs : FiniteLift.StrongClosedAmalgamation G (FiniteLift.aclSet G) (S.menuRel safe))
    (A0 : Set M) (finiteA : A0.Finite) (nonemptyA : A0.Nonempty) :
    Nonempty (SourceStage S H cco normalized A0 safe) := by
  classical
  let A := finiteA.toFinset
  have hA : (↑A : Set M) = A0 := finiteA.coe_toFinset
  have hne : A.Nonempty := by
    obtain ⟨a, ha⟩ := nonemptyA
    exact ⟨a, finiteA.mem_toFinset.mpr ha⟩
  let B := chosenJointMaster S H cco lower normalized many (↑A : Set M) A.finite_toSet
    (by exact ⟨hne.choose, hne.choose_spec⟩)
  have components : ∀ D : Direction S, Nonempty (Component S H cco normalized (↑A : Set M) safe B D) :=
    fun D => exists_component S H cco normalized A B D lower safe hs hne
  have stage : Nonempty (SourceStage S H cco normalized (↑A : Set M) safe) :=
    ⟨⟨B, fun D => Classical.choice (components D)⟩⟩
  exact hA ▸ stage

end
end CCO.RankInduction.Factors
