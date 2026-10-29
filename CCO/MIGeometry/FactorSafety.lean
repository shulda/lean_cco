import CCO.MIGeometry.SourceAssembly
import CCO.MIGeometry.SafeDescent
import CCO.AclOwners.UnsafeConcentration

/-! Conditional source corollary. The original strong CLOSED safe palette
is an explicit given premise; the structural factors require none. -/
universe v w t
namespace CCO.MIGeometry
open ParityHasse.Original RealClosure.Bounds RealHull.Geometry
open FinitePackets.Geometry FinitePackets.Normalization RawExact AclOwners
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] (cco : SemanticCCO.{0,v,0,w} S)

/-- Every canonical recipient has its globally defined FULL-support safe
palette. This invokes the actual one-sided theorem with all providers. -/
theorem canonical_factor_safety (normalized : NoFiniteExactKernel S)
    (D : Direction S) (safe : Set (Atom S))
    (amalgamate : StrongClosedAmalgamation S G safe) :
    letI := originalQuotientAction S H (hat S H cco D)
    StrongClosedAmalgamation (actualQuotientSource S H (hat S H cco D)) G
      (fullSupportPalette S H (hat S H cco D) safe) := by
  let K := complementaryCore S H cco D
  let B := ExactCRT.exactPresentation S (complementaryCore_exact S H cco D)
  have hB : evaluate S B.words = K.val.r :=
    ExactCRT.exactPresentation_represents S (complementaryCore_exact S H cco D)
  exact one_sided_full_support_safety S H (hat S H cco D) K cco
    (hatPresentation S H cco D) B (hatPresentation_represents S H cco D) hB
    (congrArg Subtype.val (hat_inf_complementary S H cco normalized D))
    (factor_recipient_harmless S H cco normalized D) safe amalgamate

/-- Every nonexceptional clique projection lies in ONE actual finite
R_i/hat_i packet. No noncollapse of quotient unsafe pairs is asserted. -/
theorem unsafe_clique_maximal_packets (normalized : NoFiniteExactKernel S)
    (h : 2 ≤ directionCount S) (safe : Set (Atom S))
    (amalgamate : StrongClosedAmalgamation S G safe) (Z : Set M) (hZ : UnsafeClique S safe Z) :
    ∃ D₀ : Direction S, ∀ E : Direction S, E ≠ D₀ → ∀ z ∈ Z, ∀ x ∈ Z,
      quotientColourEq S H (hat S H cco E) (oldCorrespondence S H cco E)
        (hat_le_correspondence S H cco E) (Quotient.mk'' z) (Quotient.mk'' x) := by
  letI := nonempty_directions_of_two S h
  obtain ⟨D₀,hD⟩ := unsafe_clique_one_exception S H cco normalized safe amalgamate Z hZ
  exact ⟨D₀,fun E hE z hz x hx =>
    (quotientColourEq_projection S H _ _ _ z x).mpr (hD E hE z hz hx)⟩

/-- Complete palette-conditional branch of the simultaneous factor
corollary. The independent structural branch remains available without S. -/
theorem canonical_maximal_factors (normalized : NoFiniteExactKernel S)
    (h : 2 ≤ directionCount S) (safe : Set (Atom S))
    (amalgamate : StrongClosedAmalgamation S G safe) :
    (∀ D : Direction S,
      letI := originalQuotientAction S H (hat S H cco D)
      StrongClosedAmalgamation (actualQuotientSource S H (hat S H cco D)) G
        (fullSupportPalette S H (hat S H cco D) safe)) ∧
    (∀ (Z : Set M), UnsafeClique S safe Z →
      ∃ D₀ : Direction S, ∀ E : Direction S, E ≠ D₀ → ∀ z ∈ Z, ∀ x ∈ Z,
        quotientColourEq S H (hat S H cco E) (oldCorrespondence S H cco E)
          (hat_le_correspondence S H cco E) (Quotient.mk'' z) (Quotient.mk'' x)) ∧
    (∀ A : Finset M, Acl G A =
      {x | ∀ D : Direction S, ∃ a ∈ A, oldCorrespondence S H cco D a x}) ∧
    jointOwner S H cco normalized ≠ ⊥ := by
  letI := nonempty_directions_of_two S h
  exact ⟨fun D => canonical_factor_safety S H cco normalized D safe amalgamate,
    fun Z hZ => unsafe_clique_maximal_packets S H cco normalized h safe amalgamate Z hZ,
    maximal_closure_bands S H cco normalized,jointOwner_ne_bot S H cco normalized⟩

end CCO.MIGeometry
