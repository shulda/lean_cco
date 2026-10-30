import CCO.RankInduction.JointMaster
import CCO.RankInduction.NestedDecorations
import CCO.RankInduction.FactorSources
import CCO.RankInduction.FactorPoints

/-! Internal materialized data for the normalized rank construction.
The receiving constructor proves existence from the bound lower-rank
hypotheses; these are not new hypotheses of the principal rank theorem. -/

universe v w t
namespace CCO.RankInduction.Factors
noncomputable section
open RawExact ExactCRT CanonicalQuotients Owners.Product Owners.Provider Owners.Master
open MIGeometry ParityHasse.Original FinitePackets.Normalization RealClosure.Bounds AclOwners

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] [Countable M] [DecidableEq M]
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,v,w} S)
variable (normalized : NoFiniteExactKernel S)
local instance sourceStageCoreInvariant (D : Direction S) : Invariant G (factorCore S H cco D).val :=
  exactInvariant S H cco (factorCore S H cco D)
local instance sourceStageOwnerInvariant (D : Direction S) :
    Invariant G (factorOwner S H cco normalized D).val :=
  exactInvariant S H cco (factorOwner S H cco normalized D)
local instance sourceStageJointInvariant : Invariant G (jointKernel S H cco normalized).val :=
  exactInvariant S H cco (jointKernel S H cco normalized)

def factorInput (A0 : Set M) (D : Direction S) : Set (Quotient (factorCore S H cco D).val) :=
  (Quotient.mk'' : M → Quotient (factorCore S H cco D).val) '' A0

def factorPalette (safe : Set (S.Atom () ())) (D : Direction S) :=
  fullSupportPalette S H (hat S H (semanticCCO_change_universe S cco) D) safe

abbrev LowerMaster (A0 : Set M) := ActualMaster.{v,v,t,v}
  (quotientSource S H cco (jointKernel S H cco normalized))
  (quotientSource_homogeneous S H cco (jointKernel S H cco normalized))
  (quotientSource_cco S H cco (jointKernel S H cco normalized))
  ((Quotient.mk'' : M → Quotient (jointKernel S H cco normalized).val) '' A0)

def factorOwners {A0 : Set M} (B : LowerMaster S H cco normalized A0) (D : Direction S) :=
  nestedImage S H cco (jointKernel S H cco normalized) (factorOwner S H cco normalized D)
    (jointKernel_le_owner S H cco normalized D) B.carrier

def factorProjection (D : Direction S) :=
  coarseProjection S H (semanticCCO_change_universe S cco) normalized D

theorem factorProjection_equivariant (D : Direction S) (g : G)
    (x : Quotient (factorCore S H cco D).val) :
    factorProjection S H cco normalized D (g • x) = g • factorProjection S H cco normalized D x :=
  quotientMap_equivariant (core_le_owner S H (semanticCCO_change_universe S cco) normalized D) g x

/-- A component is the actual finite original-language factor, retaining
its entire native original coarse owner image and all prescribed requests. -/
structure Component (A0 : Set M) (safe : Set (S.Atom () ()))
    (B : LowerMaster S H cco normalized A0) (D : Direction S) where
  carrier : Set (Quotient (factorCore S H cco D).val)
  ordinary : Witness (factorSource S H (semanticCCO_change_universe S cco) D) G
    (factorPalette S H cco safe D) (factorInput S H cco A0 D) carrier
  closed : FiniteLift.aclSet G carrier = carrier
  over : ∀ x : carrier, factorProjection S H cco normalized D x.val ∈ factorOwners S H cco normalized B D
  onto : Function.Surjective (ownerProjection (factorProjection S H cco normalized D)
    carrier (factorOwners S H cco normalized B D) over)
  prescribed : PrescribedEPPAFor
    (inducedQuotient (factorProjection S H cco normalized D)
      (factorProjection_equivariant S H cco normalized D)
      carrier (factorOwners S H cco normalized B D) over onto)
    {x | x.val ∈ factorInput S H cco A0 D}
  points : GroupActions.PrescribedLift
    (inducedQuotient (factorProjection S H cco normalized D)
      (factorProjection_equivariant S H cco normalized D)
      carrier (factorOwners S H cco normalized B D) over onto).action
    (ownerProjection (factorProjection S H cco normalized D)
      carrier (factorOwners S H cco normalized B D) over)

def Component.quotient {A0 : Set M} {safe : Set (S.Atom () ())}
    {B : LowerMaster S H cco normalized A0} {D : Direction S}
    (F : Component S H cco normalized A0 safe B D) :=
  inducedQuotient (factorProjection S H cco normalized D)
    (factorProjection_equivariant S H cco normalized D)
    F.carrier (factorOwners S H cco normalized B D) F.over F.onto

/-- Every field below is supplied by the actual strict master and B028
factor constructors. One finite master is fixed before all components. -/
structure SourceStage (A0 : Set M) (safe : Set (S.Atom () ())) where
  master : LowerMaster S H cco normalized A0
  component : ∀ D : Direction S, Component S H cco normalized A0 safe master D

end
end CCO.RankInduction.Factors
