import CCO.RankInduction.NestedOwners

/-! ONE lower-rank owner master, fixed before any source request. The
literal kernel is the actual family meet used by the joint-source
reconstruction; B023 identifies it with the strict Birkhoff owner kernel. -/

universe v w t
namespace CCO.RankInduction.Factors
noncomputable section
open RawExact ExactCRT CanonicalQuotients Owners.Product Owners.Provider Owners.Master
open MIGeometry ParityHasse.Original FinitePackets.Normalization RealClosure.Bounds AclOwners

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] [Countable M] [DecidableEq M]
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,v,w} S)

abbrev factorCore (D : Direction S) : ExactEq S H cco () :=
  Core S H (semanticCCO_change_universe S cco) D
abbrev factorOwner (normalized : NoFiniteExactKernel S) (D : Direction S) :
    ExactEq S H cco () := Owner S H (semanticCCO_change_universe S cco) normalized D

def jointKernel (normalized : NoFiniteExactKernel S) : ExactEq S H cco () :=
  ⟨Abstract.familyMeet (fun D : Direction S => (factorOwner S H cco normalized D).val),
    colourFamilyMeet_exact S (fun D => exactColour S H (semanticCCO_change_universe S cco)
      (factorOwner S H cco normalized D)) (fun D => (factorOwner S H cco normalized D).property)⟩

theorem jointKernel_eq (normalized : NoFiniteExactKernel S) :
    jointKernel S H cco normalized = Joint S H (semanticCCO_change_universe S cco) normalized := by
  apply Subtype.ext
  apply Setoid.ext
  intro x y
  exact owners_meet S H (semanticCCO_change_universe S cco) normalized x y

theorem jointKernel_ne_bot (normalized : NoFiniteExactKernel S)
    (many : 2 ≤ directionCount S) : jointKernel S H cco normalized ≠ ⊥ := by
  rw [jointKernel_eq S H cco normalized]
  exact joint_ne_bot S H (semanticCCO_change_universe S cco) normalized many

theorem jointKernel_le_owner (normalized : NoFiniteExactKernel S) (D : Direction S) :
    jointKernel S H cco normalized ≤ factorOwner S H cco normalized D :=
  fun _ _ h => h D

local instance jointMasterKernelInvariant (normalized : NoFiniteExactKernel S) :
    Invariant G (jointKernel S H cco normalized).val :=
  exactInvariant S H cco (jointKernel S H cco normalized)

/-- The bound lower U is invoked ONLY in the strictly smaller joint owner,
on the entire projected original input. Top is allowed. -/
theorem exists_joint_master (lower : Lower S G H cco)
    (normalized : NoFiniteExactKernel S) (many : 2 ≤ directionCount S)
    (A0 : Set M) (finiteA : A0.Finite) (nonemptyA : A0.Nonempty) :
    Nonempty (ActualMaster.{v,v,t,v}
      (quotientSource S H cco (jointKernel S H cco normalized))
      (quotientSource_homogeneous S H cco (jointKernel S H cco normalized))
      (quotientSource_cco S H cco (jointKernel S H cco normalized))
      ((Quotient.mk'' : M → Quotient (jointKernel S H cco normalized).val) '' A0)) := by
  have bound := lower (jointKernel S H cco normalized) (jointKernel_ne_bot S H cco normalized many)
  exact bound.2.2 _ (finiteA.image _) (nonemptyA.image _)

def chosenJointMaster (lower : Lower S G H cco)
    (normalized : NoFiniteExactKernel S) (many : 2 ≤ directionCount S)
    (A0 : Set M) (finiteA : A0.Finite) (nonemptyA : A0.Nonempty) :=
  Classical.choice (exists_joint_master S H cco lower normalized many A0 finiteA nonemptyA)

end
end CCO.RankInduction.Factors
