import CCO.AclOwners.Correspondence
import CCO.AclOwners.QuotientSource
import CCO.FinitePackets.Geometry.ExactCutSource

/-! The structural gluing dichotomy and original, nonmaximal packet
cores. Normalization is used only for the explicitly finite exact meets.
No safe palette, EPPA or owner-master input is present. -/
universe v w t
namespace CCO.AclOwners
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Geometry FinitePackets.Normalization RawExact
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] (cco : SemanticCCO.{0,v,0,w} S)

theorem normalized_exact_finite (normalized : NoFiniteExactKernel S)
    (E : ColourEq S ()) (hE : ExactCRT.IsExactEq S (i := ()) E.val)
    (hfin : FiniteClasses S E) : E = ⊥ := by
  obtain ⟨B,hB⟩ := hE
  exact normalized E ((finiteIndex_bottom_iff_finite_classes S E).mpr hfin) B hB

include H in
theorem core_exact (E : ColourEq S ()) : ExactCRT.IsExactEq S (i := ()) (core S E).val :=
  ⟨coreExact S H E,coreExact_represents S H E⟩

include H cco in
theorem core_infinite_of_infinite (E : ColourEq S ()) (hE : ¬ FiniteClasses S E) :
    ¬ FiniteClasses S (core S E) := by
  intro hcore
  apply hE
  apply (finiteIndex_bottom_iff_finite_classes S E).mp
  exact finiteIndex_trans S ⊥ (core S E) E bot_le (core_le S E)
    ((finiteIndex_bottom_iff_finite_classes S _).mpr hcore) (finiteIndex_core S H cco E)

theorem correspondence_core_disjoint (normalized : NoFiniteExactKernel S)
    (E : ColourEq S ()) (hE : ExactCRT.IsExactEq S (i := ()) E.val) :
    E ⊓ core S (correspondenceEq S H cco E hE) = ⊥ := by
  apply normalized_exact_finite S normalized
    (E ⊓ core S (correspondenceEq S H cco E hE))
    (ExactCRT.isExactEq_inf S hE (core_exact S H _))
  apply finiteClasses_of_le S (F := finitePacket S H) ?_ (finitePacket_finite S H)
  intro x y hxy
  exact ((correspondence_inf_eq_packet S H cco normalized E).mp
    ⟨hxy.1,core_le S _ hxy.2⟩).2

/-- C10: if the global cut is not the finite packet, its actual packet
core is an infinite nonidentity exact complementary kernel. Both actual
quotient diversity palettes strictly decrease. -/
theorem correspondence_gluing_dichotomy (normalized : NoFiniteExactKernel S)
    (E : ColourEq S ()) (hE : ExactCRT.IsExactEq S (i := ()) E.val) (hne : E ≠ ⊥) :
    correspondenceEq S H cco E hE = finitePacket S H ∨
      ∃ C : ColourEq S (), ¬ FiniteClasses S C ∧ C ≠ ⊥ ∧
        ExactCRT.IsExactEq S (i := ()) C.val ∧ E ⊓ C = ⊥ ∧
        Nat.card ((actualQuotientSource S H E).Atom () ()) < Nat.card (Atom S) ∧
        Nat.card ((actualQuotientSource S H C).Atom () ()) < Nat.card (Atom S) := by
  classical
  let R := correspondenceEq S H cco E hE
  by_cases hR : R = finitePacket S H
  · exact Or.inl hR
  · right
    have hRinf : ¬ FiniteClasses S R := by
      intro hf
      exact hR (le_antisymm (le_finitePacket S H R hf)
        (fun _ _ h => packet_le_correspondence S H normalized E h))
    have hCinf := core_infinite_of_infinite S H cco R hRinf
    have hCne : core S R ≠ ⊥ := fun he => hCinf (he ▸ finiteClasses_bot S)
    refine ⟨core S R,hCinf,hCne,core_exact S H R,
      correspondence_core_disjoint S H cco normalized E hE,?_,?_⟩
    · letI := S.finiteAtom () ()
      letI := (actualQuotientSource S H E).finiteAtom () ()
      simpa only [Nat.card_eq_fintype_card] using quotient_palette_strictly_drops S H E hne
    · letI := S.finiteAtom () ()
      letI := (actualQuotientSource S H (core S R)).finiteAtom () ()
      simpa only [Nat.card_eq_fintype_card] using quotient_palette_strictly_drops S H (core S R) hCne

theorem direction_minimalCut (D : Direction S) : MinimalInfiniteCut S D.val := by
  refine ⟨fun h => D.property.1 ((finiteIndex_bottom_iff_finite_classes S _).mp h),?_⟩
  intro E hE
  exact (finiteIndex_bottom_iff_finite_classes S E).mpr (D.property.2 E hE)

noncomputable def oldCorrespondence (D : Direction S) : ColourEq S () :=
  correspondenceEq S H cco D.val (direction_exact S H cco D)

noncomputable def oldCore (D : Direction S) : ColourEq S () :=
  core S (oldCorrespondence S H cco D)

include H cco in
theorem distinct_directions_meet_identity (normalized : NoFiniteExactKernel S)
    (D E : Direction S) (hne : D ≠ E) : D.val ⊓ E.val = ⊥ :=
  normalized_exact_finite S normalized (D.val ⊓ E.val)
    (ExactCRT.isExactEq_inf S (direction_exact S H cco D) (direction_exact S H cco E))
    (distinct_direction_inf_finite S D.property E.property (fun h => hne (Subtype.ext h)))

theorem disjoint_le_correspondence (E F : ColourEq S ())
    (hEF : E ⊓ F = ⊥) : ∀ x y, F x y → correspondence S E x y := by
  intro x y hF u v hE hsq
  obtain ⟨z,huz,hzv⟩ := hsq
  have hFuz : F u z := (F.property x y u z huz.symm).mp hF
  have hFzv : F z v := (F.property x y z v hzv.symm).mp hF
  have hh : (E ⊓ F) u v := ⟨hE,F.val.trans hFuz hFzv⟩
  rwa [hEF] at hh

/-- C12: every other minimal infinite direction is in the ORIGINAL
correspondence, before taking its packet core. -/
theorem direction_le_other_correspondence (normalized : NoFiniteExactKernel S)
    (D E : Direction S) (hne : D ≠ E) : E.val ≤ oldCorrespondence S H cco D :=
  disjoint_le_correspondence S D.val E.val (distinct_directions_meet_identity S H cco normalized D E hne)

/-- C16's monotone packet-core consequence; these cores are not the
maximal pseudocomplements prepared in later packages. -/
theorem direction_le_other_core (normalized : NoFiniteExactKernel S)
    (D E : Direction S) (hne : D ≠ E) : E.val ≤ oldCore S H cco D := by
  have he := minimal_cut_eq_core S H cco (direction_minimalCut S E)
  rw [he]
  exact core_mono S (direction_le_other_correspondence S H cco normalized D E hne)

theorem oldCore_disjoint (normalized : NoFiniteExactKernel S) (D : Direction S) :
    D.val ⊓ oldCore S H cco D = ⊥ :=
  correspondence_core_disjoint S H cco normalized D.val (direction_exact S H cco D)

theorem oldCore_infinite_of_other (normalized : NoFiniteExactKernel S)
    (D E : Direction S) (hne : D ≠ E) : ¬ FiniteClasses S (oldCore S H cco D) := by
  intro hf
  exact E.property.1 (finiteClasses_of_le S
    (direction_le_other_core S H cco normalized D E hne) hf)

end CCO.AclOwners
