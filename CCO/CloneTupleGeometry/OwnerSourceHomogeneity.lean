import CCO.CloneTupleGeometry.OwnerHomogeneity
import CCO.CloneTupleGeometry.TypedSourceHomogeneity

/-!
# B060 C11/N02: homogeneity and ordinary AP of the actual owner successor

The source is the genuine owner child of the B047 maximal-character
marked limit, not an arbitrary unary expansion. The actual marked source
was already identified with its infinite pure clone source. Apply the
proved clone-to-owner finite-diagram descent to this exact identification.

This closes the homogeneity/AP part of C11. Owner CCO is transported in
the separate `OwnerSourceCCO` module. Reasonableness, finite safe-tower
iteration and the four final B060 exports remain separate obligations.
-/

universe u v w t
namespace CCO.CloneTupleGeometry

open APCharacter
open APCharacter.SourceAge
open RigidGroupoid.Geometry
open TerminalPowers
noncomputable section

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]
variable (H : HomogeneousSource S G) (ap : AgeAP S)
variable (C : ExactCalculus (CloneSAP.source S))
variable {r : ι} {A : Kernel (CloneSAP.source S) r}
variable (P : SourcePhase (CloneSAP.source S) (CloneSAP.homogeneous S H) C A)
variable (cco : SemanticCCO.{u,v,max u v,w} S)

-- As in the preceding concrete source theorem, dependent FullAut indices
-- require local elaboration budgets; no mathematical premise is changed.
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 900000

include ap in
/-- The true owner child of the actual marked B047 successor is
homogeneous under its own FULL colour-preserving automorphism group. -/
theorem actual_marked_owner_homogeneous
    (I : CloneMarkedIdentification S H C P cco) :
    HomogeneousSource (owner_child_source S H ap C P cco I)
      (FullAut (owner_child_source S H ap C P cco I)) := by
  exact owner_homogeneous_of_clone
    (owner_child_source S H ap C P cco I)
    (actual_marked_owner_clone_homogeneous S H ap C P cco I)

include ap in
/-- Ordinary AP of the same actual owner age. The quotient can retain
algebraicity, so strong amalgamation is not asserted for owners. -/
theorem actual_marked_owner_ageAP
    (I : CloneMarkedIdentification S H C P cco) :
    AgeAP (owner_child_source S H ap C P cco I) := by
  exact ageAP_of_homogeneous
    (owner_child_source S H ap C P cco I)
    (actual_marked_owner_homogeneous S H ap C P cco I)

include ap in
/-- With the ORIGINAL countable source hypotheses, B047 constructs
the identification itself. Thus the actual owner homogeneity/AP source
instance is discharged rather than left behind an extra provider. -/
theorem actual_clone_marked_owner_homogeneous_ageAP
    [∀ i : ι, Countable (X i)] :
    ∃ I : CloneMarkedIdentification S H C P cco,
      HomogeneousSource (owner_child_source S H ap C P cco I)
        (FullAut (owner_child_source S H ap C P cco I)) ∧
      AgeAP (owner_child_source S H ap C P cco I) := by
  let I := actualCloneIdentification S H C P cco
  exact ⟨I,actual_marked_owner_homogeneous S H ap C P cco I,
    actual_marked_owner_ageAP S H ap C P cco I⟩

end
end CCO.CloneTupleGeometry
