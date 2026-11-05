import CCO.CloneTupleGeometry.OwnerSourceHomogeneity
import CCO.CloneTupleGeometry.TypedSourceCCO
import CCO.APCharacter.SourceAge.UnarySourceCCO
import CCO.CloneSAP.Amalgamation

/-!
# B060 N02: actual marked-owner CCO and the next pure-clone SAP source

B047 proves HOM CCO for its genuine marked Fraisse source. Transport it
through the already constructed complete typed source isomorphism and
project the actual pure clone homomorphism to its owner source. Together
with owner AP this recovers SAP for the owner's pure clone, ready for
another genuine safe phase. No SAP of the OWNER quotient is asserted.

The finite terminal tower and source reasonableness are still separate.
-/

universe u v w t z
namespace CCO.CloneTupleGeometry

open APCharacter
open APCharacter.SourceAge
open RigidGroupoid.Geometry
noncomputable section

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]
variable (H : HomogeneousSource S G) (ap : AgeAP S)
variable (C : ExactCalculus (CloneSAP.source S))
variable {r : ι} {A : Kernel (CloneSAP.source S) r}
variable (P : SourcePhase (CloneSAP.source S) (CloneSAP.homogeneous S H) C A)
variable (cco : SemanticCCO.{u,v,max u v,w} S)

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 900000

include ap in
/-- Actual HOM CCO of the SAME complete marked successor written
as the pure clone of its true owner source. All missing edges and
independent noninjective cycle witnesses retain their original meaning. -/
theorem actual_marked_owner_clone_semanticCCO
    (I : CloneMarkedIdentification S H C P cco) :
    SemanticCCO.{u,v,z,w}
      (CloneSAP.source (owner_child_source S H ap C P cco I)) := by
  exact TypedAtomicSourceEquiv.semanticCCO_pullback
    (actual_marked_owner_clone_source_equiv S H ap C P cco I)
    (UnarySource.semanticCCO I)

include ap in
/-- HOM CCO of the actual owner source follows by the proved literal
clone-owner projection, with no hidden owner SAP or new provider. -/
theorem actual_marked_owner_semanticCCO
    (I : CloneMarkedIdentification S H C P cco) :
    SemanticCCO.{u,v,z,w} (owner_child_source S H ap C P cco I) := by
  exact CloneSAP.CCO.cco_reflects
    (owner_child_source S H ap C P cco I)
    (actual_marked_owner_clone_semanticCCO S H ap C P cco I)

include ap in
/-- The owner successor's actual pure clone has SAP, by its proved
ordinary owner AP. The conclusion applies to this concrete next source. -/
theorem actual_marked_owner_clone_ageSAP
    (I : CloneMarkedIdentification S H C P cco) :
    AgeSAP (CloneSAP.source (owner_child_source S H ap C P cco I)) := by
  exact CloneSAP.strong_amalgamation
    (owner_child_source S H ap C P cco I)
    (actual_marked_owner_ageAP S H ap C P cco I)

end
end CCO.CloneTupleGeometry
