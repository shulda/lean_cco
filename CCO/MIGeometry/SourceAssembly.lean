import CCO.MIGeometry.FactorOwners
import CCO.MIGeometry.BirkhoffGeometry
import CCO.MIGeometry.ClosureBands

/-! Simultaneous structural factors of the actual normalized original
source. Safe palettes remain in the separate conditional assembly. -/
universe v w t
namespace CCO.MIGeometry
open ParityHasse.Original RealClosure.Bounds
open FinitePackets.Geometry FinitePackets.Normalization RawExact AclOwners
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] (cco : SemanticCCO.{0,v,0,w} S)

theorem nonempty_directions_of_two (h : 2 ≤ directionCount S) : Nonempty (Direction S) := by
  classical
  letI : Fintype (Direction S) := Fintype.ofFinite _
  apply Fintype.card_pos_iff.mp
  have hh : 2 ≤ Fintype.card (Direction S) := by
    simpa only [directionCount,Nat.card_eq_fintype_card] using h
  omega

/-- The literal hat factor remains normalized, with no nonexact finite
packet being declared identity. -/
theorem hatQuotient_normalized (normalized : NoFiniteExactKernel S) (D : Direction S) :
    NoFiniteExactKernel (actualQuotientSource S H (hat S H cco D)) := by
  have hh := selectedQuotient_normalized S H cco normalized {D}
  rw [selectedHat_singleton S H cco D] at hh
  exact hh

theorem hatQuotient_infinite (normalized : NoFiniteExactKernel S) (D : Direction S) :
    Infinite (Quotient (hat S H cco D).val) := by
  have hh := selectedQuotient_infinite S H cco normalized {D} (Set.singleton_nonempty D)
  rw [selectedHat_singleton S H cco D] at hh
  exact hh

/-- Full canonical-language source inheritance, kept separate from rank
counting and mathematical normalization. -/
theorem hatQuotient_source (D : Direction S) :
    letI := originalQuotientAction S H (hat S H cco D)
    HomogeneousSource (actualQuotientSource S H (hat S H cco D)) G ∧
      SemanticCCO.{0,v,0,v} (actualQuotientSource S H (hat S H cco D)) :=
  ⟨actualQuotient_homogeneous S H _ (hatPresentation S H cco D)
      (hatPresentation_represents S H cco D) cco,
    actualQuotient_CCO S H _ (hatPresentation S H cco D)
      (hatPresentation_represents S H cco D) cco⟩

noncomputable def jointOwnerPresentation (normalized : NoFiniteExactKernel S) : NonemptyExact S () () :=
  ExactCRT.exactPresentation S (jointOwner_exact S H cco normalized)

theorem jointOwnerPresentation_represents (normalized : NoFiniteExactKernel S) :
    evaluate S (jointOwnerPresentation S H cco normalized).words =
      (jointOwner S H cco normalized).val.r :=
  ExactCRT.exactPresentation_represents S (jointOwner_exact S H cco normalized)

/-- Hstar may equal Top; the inherited owner source may therefore be the
singleton, without invalidating either inheritance or strict rank decrease. -/
theorem jointOwner_source (normalized : NoFiniteExactKernel S) :
    letI := originalQuotientAction S H (jointOwner S H cco normalized)
    HomogeneousSource (actualQuotientSource S H (jointOwner S H cco normalized)) G ∧
      SemanticCCO.{0,v,0,v} (actualQuotientSource S H (jointOwner S H cco normalized)) :=
  ⟨actualQuotient_homogeneous S H _ (jointOwnerPresentation S H cco normalized)
      (jointOwnerPresentation_represents S H cco normalized) cco,
    actualQuotient_CCO S H _ (jointOwnerPresentation S H cco normalized)
      (jointOwnerPresentation_represents S H cco normalized) cco⟩

/-- Structural branch of the source corollary: actual strict joint owner,
JOG, normalized unary infinite factors, strict ranks, and finite-input acl.
Every provider is instantiated; there is no safe/SAP/EPPA input. -/
theorem canonical_maximal_factor_structure (normalized : NoFiniteExactKernel S)
    (h : 2 ≤ directionCount S) :
    jointOwner S H cco normalized ≠ ⊥ ∧
    Nat.card ((actualQuotientSource S H (jointOwner S H cco normalized)).Atom () ()) <
      Nat.card (S.Atom () ()) ∧
    (∀ D E : Direction S, D ≠ E →
      ownerExact S H cco normalized D ⊔ ownerExact S H cco normalized E =
        hatExact S H cco D ⊔ hatExact S H cco E) ∧
    (∀ D : Direction S,
      NoFiniteExactKernel (actualQuotientSource S H (hat S H cco D)) ∧
      Infinite (Quotient (hat S H cco D).val) ∧
      directionCount (actualQuotientSource S H (hat S H cco D)) = 1 ∧
      Nat.card ((actualQuotientSource S H (hat S H cco D)).Atom () ()) < Nat.card (S.Atom () ())) ∧
    (∀ A : Finset M, Acl G A =
      {x | ∀ D : Direction S, ∃ a ∈ A, oldCorrespondence S H cco D a x}) := by
  letI := nonempty_directions_of_two S h
  exact ⟨jointOwner_ne_bot S H cco normalized,
    jointOwner_quotient_rank_drop S H cco normalized,
    ownerExact_JOG S H cco normalized,
    fun D => ⟨hatQuotient_normalized S H cco normalized D,
      hatQuotient_infinite S H cco normalized D,
      hat_quotient_directionCount S H cco normalized D,
      hat_quotient_rank_drop S H cco normalized h D⟩,
    maximal_closure_bands S H cco normalized⟩

end CCO.MIGeometry
