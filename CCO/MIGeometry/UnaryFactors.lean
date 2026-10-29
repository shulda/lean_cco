import CCO.MIGeometry.SelectedNormalization

/-! Finite-index Sigma geometry and actual unary closure of each maximal
factor. None of these statements needs a safe palette. -/
universe v w t
namespace CCO.MIGeometry
open ParityHasse.Original RealClosure.Bounds RealHull.Geometry
open FinitePackets.Geometry FinitePackets.Normalization RawExact AclOwners
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] (cco : SemanticCCO.{0,v,0,w} S)

theorem exists_other_direction (h : 2 ≤ directionCount S) (D : Direction S) :
    ∃ E : Direction S, D ≠ E := by
  classical
  by_contra hn
  push_neg at hn
  letI : Subsingleton (Direction S) := ⟨fun a b => (hn a).symm.trans (hn b)⟩
  letI : Fintype (Direction S) := Fintype.ofFinite _
  have hc : Fintype.card (Direction S) ≤ 1 := Fintype.card_le_one_iff_subsingleton.mpr inferInstance
  have hh : 2 ≤ Fintype.card (Direction S) := by
    simpa only [directionCount,Nat.card_eq_fintype_card] using h
  omega

theorem oldCore_hat_finiteIndex (D : Direction S) :
    FiniteIndex S (oldCore S H cco D) (hat S H cco D) :=
  finiteIndex_lower S (hat_le_correspondence S H cco D)
    (finiteIndex_core S H cco (oldCorrespondence S H cco D))

theorem hat_correspondence_finiteIndex (D : Direction S) :
    FiniteIndex S (hat S H cco D) (oldCorrespondence S H cco D) :=
  finiteIndex_upper S (oldCore_le_hat S H cco D)
    (finiteIndex_core S H cco (oldCorrespondence S H cco D))

theorem hat_sigma (normalized : NoFiniteExactKernel S) (D : Direction S) :
    sigma S H (hat S H cco D) = oldCorrespondence S H cco D :=
  (sigma_eq_of_finiteIndex S H (oldCore_le_hat S H cco D)
    (oldCore_hat_finiteIndex S H cco D)).symm.trans
      (oldCore_sigma S H cco normalized D)

noncomputable def hatPresentation (D : Direction S) : NonemptyExact S () () :=
  ExactCRT.exactPresentation S (hat_exact S H cco D)

theorem hatPresentation_represents (D : Direction S) :
    evaluate S (hatPresentation S H cco D).words = (hat S H cco D).val.r :=
  ExactCRT.exactPresentation_represents S (hat_exact S H cco D)

/-- The inherited source and the strict palette count are separate outputs. -/
theorem hat_quotient_rank_drop (normalized : NoFiniteExactKernel S)
    (h : 2 ≤ directionCount S) (D : Direction S) :
    Nat.card ((actualQuotientSource S H (hat S H cco D)).Atom () ()) < Nat.card (Atom S) := by
  obtain ⟨E,hE⟩ := exists_other_direction S h D
  letI := S.finiteAtom () ()
  letI := (actualQuotientSource S H (hat S H cco D)).finiteAtom () ()
  simpa only [Nat.card_eq_fintype_card] using quotient_palette_strictly_drops S H
    (hat S H cco D) (hat_ne_bot_of_other S H cco normalized D E hE)

theorem hat_quotient_directionCount (normalized : NoFiniteExactKernel S)
    (D : Direction S) : directionCount (actualQuotientSource S H (hat S H cco D)) = 1 := by
  obtain ⟨hst,hleast⟩ := oldCorrespondence_least_upper S H cco normalized D
  exact quotient_directionCount_one S H (hat S H cco D) (oldCorrespondence S H cco D)
    (hat_le_correspondence S H cco D) (hatPresentation S H cco D)
    (hatPresentation_represents S H cco D) cco (hat_sigma S H cco normalized D) _ hst hleast

/-- R_i/hat_i is the genuine greatest finite invariant relation, including
all nonexact relations of the quotient language. -/
theorem hat_quotient_finite_bottom (normalized : NoFiniteExactKernel S) (D : Direction S) :
    letI := originalQuotientAction S H (hat S H cco D)
    let qH := actualQuotient_homogeneous S H (hat S H cco D)
      (hatPresentation S H cco D) (hatPresentation_represents S H cco D) cco
    quotientColourEq S H (hat S H cco D) (oldCorrespondence S H cco D)
      (hat_le_correspondence S H cco D) =
        finitePacket (actualQuotientSource S H (hat S H cco D)) qH := by
  obtain ⟨hst,hleast⟩ := oldCorrespondence_least_upper S H cco normalized D
  exact (quotient_finite_bottom S H (hat S H cco D) (oldCorrespondence S H cco D)
    (hat_le_correspondence S H cco D) (hatPresentation S H cco D)
    (hatPresentation_represents S H cco D) cco (hat_sigma S H cco normalized D) _ hst hleast).1

/-- EVERY finite input, including empty, has unary real closure in the
literal original correspondence packet. No original SAP premise is used. -/
theorem hat_quotient_acl (normalized : NoFiniteExactKernel S) (D : Direction S)
    (A : Finset (Quotient (hat S H cco D).val)) (x : Quotient (hat S H cco D).val) :
    letI := originalQuotientAction S H (hat S H cco D)
    x ∈ Acl G A ↔ ∃ a ∈ A, quotientColourEq S H (hat S H cco D)
      (oldCorrespondence S H cco D) (hat_le_correspondence S H cco D) a x := by
  obtain ⟨hst,hleast⟩ := oldCorrespondence_least_upper S H cco normalized D
  exact quotient_acl_iff_relation S H (hat S H cco D) (oldCorrespondence S H cco D)
    (hat_le_correspondence S H cco D) (hatPresentation S H cco D)
    (hatPresentation_represents S H cco D) cco (hat_sigma S H cco normalized D) _ hst hleast A x

end CCO.MIGeometry
