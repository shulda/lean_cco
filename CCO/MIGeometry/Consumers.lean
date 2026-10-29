import CCO.MIGeometry.FactorSafety
import CCO.AclOwners.ClosedPreimages
import CCO.MIGeometry.PhaseDiagnostics

/-! A genuine finite absolutely closed source consumer of the complete
maximal-coordinate construction. It instantiates the general finite-kernel
provider, with no compatible-tuple or EPPA premise. -/
universe v w t
namespace CCO.MIGeometry
open ParityHasse.Original RealClosure.Bounds
open FinitePackets.Geometry FinitePackets.Normalization RawExact AclOwners
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] (cco : SemanticCCO.{0,v,0,w} S)

/-- Finite closed targets in the ACTUAL normalized maximal factors yield
one finite FULL original preimage, absolutely closed under FULL source
automorphisms. Every selected target and every empty-input boundary keeps
its literal meaning. No safe palette is used in this consumer. -/
theorem maximal_closed_targets (normalized : NoFiniteExactKernel S)
    (U : ∀ D : Direction S, Finset (Quotient (hat S H cco D).val))
    (hne : (fullPreimage
      (fun D => (Quotient.mk'' : M → Quotient (hat S H cco D).val)) U).Nonempty) :
    letI : ∀ D, MulAction G (Quotient (hat S H cco D).val) :=
      fun D => originalQuotientAction S H (hat S H cco D)
    letI : ∀ D, DecidableEq (Quotient (hat S H cco D).val) := fun _ => Classical.decEq _
    (∀ D, Acl G (U D) = (U D : Set (Quotient (hat S H cco D).val))) →
    ∃ W : Finset M, W.Nonempty ∧
      (∀ x, x ∈ W ↔ ∀ D, (Quotient.mk'' x : Quotient (hat S H cco D).val) ∈ U D) ∧
      FullRealAcl S W = (W : Set M) := by
  classical
  letI : ∀ D, MulAction G (Quotient (hat S H cco D).val) :=
    fun D => originalQuotientAction S H (hat S H cco D)
  letI : ∀ D, DecidableEq (Quotient (hat S H cco D).val) := fun _ => Classical.decEq _
  intro hU
  obtain ⟨W,hW,hmem,hclosed⟩ := exact_closed_preimages S H cco (hat S H cco)
    (hatPresentation S H cco) (hatPresentation_represents S H cco)
    (hat_joint_finite S H cco normalized) U hne hU
  exact ⟨W,hW,hmem,(fullRealAcl_eq S H W).trans hclosed⟩

end CCO.MIGeometry
