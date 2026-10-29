import CCO.AclOwners.ClosureBands
import CCO.AclOwners.UnsafeConcentration
import CCO.AclOwners.HarmlessFullAut
import CCO.AclOwners.ClosedPreimages
import CCO.AclOwners.Rectangle
import CCO.AclOwners.Controls

/-! Actual source consumers. The structural closed-target construction
uses ALL original minimal-direction coordinates and no safe palette.
Unsafe clique projection is a separate closed-amalgamation branch. -/
universe v w t
namespace CCO.AclOwners
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Geometry FinitePackets.Normalization RawExact
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] (cco : SemanticCCO.{0,v,0,w} S)

/-- A genuine finite closed consumer of the complete original coordinate
family. Each target is absolutely closed in its own ACTUAL quotient.
No common owner is required to be closed or harmless, and no coordinate
surjectivity or compatible-tuple provider is an input. -/
theorem canonical_closed_targets (normalized : NoFiniteExactKernel S)
    (U : ∀ D : Direction S, Finset (Quotient (oldCore S H cco D).val))
    (hne : (fullPreimage
      (fun D => (Quotient.mk'' : M → Quotient (oldCore S H cco D).val)) U).Nonempty) :
    letI : ∀ D, MulAction G (Quotient (oldCore S H cco D).val) :=
      fun D => originalQuotientAction S H (oldCore S H cco D)
    letI : ∀ D, DecidableEq (Quotient (oldCore S H cco D).val) := fun _ => Classical.decEq _
    (∀ D, Acl G (U D) = (U D : Set (Quotient (oldCore S H cco D).val))) →
    ∃ W : Finset M, W.Nonempty ∧
      (∀ x, x ∈ W ↔ ∀ D, (Quotient.mk'' x : Quotient (oldCore S H cco D).val) ∈ U D) ∧
      FullRealAcl S W = (W : Set M) := by
  classical
  letI : ∀ D, MulAction G (Quotient (oldCore S H cco D).val) :=
    fun D => originalQuotientAction S H (oldCore S H cco D)
  letI : ∀ D, DecidableEq (Quotient (oldCore S H cco D).val) := fun _ => Classical.decEq _
  intro hU
  obtain ⟨W,hW,hmem,hclosed⟩ := exact_closed_preimages S H cco (oldCore S H cco)
    (fun D => coreExact S H (oldCorrespondence S H cco D))
    (fun D => coreExact_represents S H _) (oldCore_joint_finite S H cco normalized) U hne hU
  exact ⟨W,hW,hmem,(fullRealAcl_eq S H W).trans hclosed⟩

/-- C20's conditional clique clause, in the literal finite quotient
packets. Every nonexceptional coordinate uses the SAME chosen real root. -/
theorem unsafe_clique_quotient_packets [Infinite M]
    (normalized : NoFiniteExactKernel S) (safe : Set (Atom S))
    (amalgamate : StrongClosedAmalgamation S G safe) (Z : Set M) (hZ : UnsafeClique S safe Z) :
    ∃ D₀ : Direction S, ∀ E : Direction S, E ≠ D₀ → ∀ z ∈ Z, ∀ x ∈ Z,
      oldFiniteBottom S H cco E (Quotient.mk'' z) (Quotient.mk'' x) := by
  letI : Nonempty (Direction S) := direction_nonempty_of_infinite S
  obtain ⟨D₀,hD⟩ := unsafe_clique_one_exception S H cco normalized safe amalgamate Z hZ
  exact ⟨D₀,fun E hE z hz x hx => (oldFiniteBottom_projection S H cco E z x).mpr
    (hD E hE z hz hx)⟩

end CCO.AclOwners
