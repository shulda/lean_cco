import CCO.MIGeometry.IntervalAtoms

/-! The exact residual-interval atoms are precisely the surviving selected
original directions. The conclusion quantifies over the FULL quotient
invariant lattice, whose distributivity is not assumed. -/
universe v w t
namespace CCO.MIGeometry
open ParityHasse.Original RealClosure.Bounds
open FinitePackets.Geometry FinitePackets.Normalization RawExact AclOwners
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] (cco : SemanticCCO.{0,v,0,w} S)

noncomputable def selectedPresentation (I : Set (Direction S)) : NonemptyExact S () () :=
  ExactCRT.exactPresentation S (selectedHat_exact S H cco I)

theorem selectedPresentation_represents (I : Set (Direction S)) :
    evaluate S (selectedPresentation S H cco I).words = (selectedHat S H cco I).val.r :=
  ExactCRT.exactPresentation_represents S (selectedHat_exact S H cco I)

noncomputable def survivingEq (I : Set (Direction S)) (D : Direction S) :
    ColourEq (actualQuotientSource S H (selectedHat S H cco I)) () :=
  quotientColourEq S H (selectedHat S H cco I)
    (ColourEq.join S H D.val (selectedHat S H cco I))
    (by letI := ColourEq.lattice S H (i := ()); exact le_sup_right)

theorem survivingEq_exact (I : Set (Direction S)) (D : Direction S) :
    ExactCRT.IsExactEq (actualQuotientSource S H (selectedHat S H cco I)) (i := ())
      (survivingEq S H cco I D).val := by
  apply quotientColourEq_exact S H cco _ (selectedPresentation S H cco I)
    (selectedPresentation_represents S H cco I)
  exact ExactCRT.isExactEq_sup S H (semanticCCO_change_universe S cco)
    (direction_exact S H cco D) (selectedHat_exact S H cco I)

theorem survivingEq_ne_bot (normalized : NoFiniteExactKernel S)
    (I : Set (Direction S)) (D : Direction S) (hD : D ∈ I) :
    survivingEq S H cco I D ≠ ⊥ := by
  letI := ColourEq.lattice S H (i := ())
  intro hz
  have hp := congrArg (quotientPullback S H (selectedHat S H cco I)) hz
  simp only [survivingEq,quotientPullback_quotientColourEq,quotientPullback_bot] at hp
  have hle : D.val ≤ selectedHat S H cco I := hp ▸ le_sup_left
  have hd : D.val = ⊥ := by
    rw [← direction_inf_selectedHat S H cco normalized I D hD]
    exact (inf_eq_left.mpr hle).symm
  exact D.property.1 (hd ▸ finiteClasses_bot S)

/-- Each selected atom gives an ACTUAL minimal infinite quotient direction. -/
theorem survivingEq_isDirection (normalized : NoFiniteExactKernel S)
    (I : Set (Direction S)) (D : Direction S) (hD : D ∈ I) :
    IsDirection (actualQuotientSource S H (selectedHat S H cco I))
      (survivingEq S H cco I D) := by
  classical
  let K := selectedHat S H cco I
  let B := selectedPresentation S H cco I
  have hB := selectedPresentation_represents S H cco I
  letI := originalQuotientAction S H K
  let T := actualQuotientSource S H K
  let qH := actualQuotient_homogeneous S H K B hB cco
  let qCCO : SemanticCCO.{0,v,0,v} T := actualQuotient_CCO S H K B hB cco
  apply direction_of_exact_minimal T qH qCCO (selectedQuotient_normalized S H cco normalized I)
    (survivingEq S H cco I D) (survivingEq_exact S H cco I D)
    (survivingEq_ne_bot S H cco normalized I D hD)
  intro F hF hle
  have hpF := quotientPullback_exact S H cco K B hB F hF
  have hpLe : quotientPullback S H K F ≤ ColourEq.join S H D.val K := by
    intro x y hxy
    exact (quotientColourEq_projection S H K _ _ x y).mp (hle hxy)
  obtain hz | he := direction_join_interval S H cco normalized D K
    (quotientPullback S H K F) (selectedHat_exact S H cco I) hpF
    (le_quotientPullback S H K F) hpLe
  · exact Or.inl (quotientPullback_injective S H K (hz.trans (quotientPullback_bot S H K).symm))
  · exact Or.inr (quotientPullback_injective S H K
      (he.trans (quotientPullback_quotientColourEq S H K _ _).symm))

include H cco in
/-- A nonzero exact meet with a normalized direction contains that atom. -/
theorem direction_le_of_exact_meet_ne_bot (normalized : NoFiniteExactKernel S)
    (D : Direction S) (E : ColourEq S ()) (hE : ExactCRT.IsExactEq S (i := ()) E.val)
    (hne : E ⊓ D.val ≠ ⊥) : D.val ≤ E := by
  by_contra hn
  have hlt : E ⊓ D.val < D.val := lt_of_le_of_ne inf_le_right (by
    intro he
    exact hn (by rw [← he]; exact inf_le_left))
  exact hne (normalized_exact_finite S normalized _
    (ExactCRT.isExactEq_inf S hE (direction_exact S H cco D)) (D.property.2 _ hlt))

/-- No additional FULL invariant minimal infinite directions occur. -/
theorem selected_direction_exhaustive (normalized : NoFiniteExactKernel S)
    (I : Set (Direction S))
    (E : Direction (actualQuotientSource S H (selectedHat S H cco I))) :
    ∃ D : I, E.val = survivingEq S H cco I D.val := by
  classical
  let K := selectedHat S H cco I
  let B := selectedPresentation S H cco I
  have hB := selectedPresentation_represents S H cco I
  letI := originalQuotientAction S H K
  let T := actualQuotientSource S H K
  let qH := actualQuotient_homogeneous S H K B hB cco
  let qCCO : SemanticCCO.{0,v,0,v} T := actualQuotient_CCO S H K B hB cco
  have hqE := direction_exact T qH qCCO E
  have hpE := quotientPullback_exact S H cco K B hB E.val hqE
  have hnK : ¬ quotientPullback S H K E.val ≤ K := by
    intro h
    have he := le_antisymm h (le_quotientPullback S H K E.val)
    have hz : E.val = ⊥ := quotientPullback_injective S H K
      (he.trans (quotientPullback_bot S H K).symm)
    exact E.property.1 (hz ▸ finiteClasses_bot T)
  have hex : ∃ D : I, ¬ quotientPullback S H K E.val ≤ hat S H cco D.val := by
    by_contra hn
    push_neg at hn
    exact hnK (fun _ _ hxy D => hn D hxy)
  obtain ⟨D,hD⟩ := hex
  have hmeet : quotientPullback S H K E.val ⊓ D.val.val ≠ ⊥ :=
    fun hz => hD ((le_hat_iff S H cco normalized D.val _ hpE).mpr hz)
  have hdE := direction_le_of_exact_meet_ne_bot S H cco normalized D.val _ hpE hmeet
  have hsurv : survivingEq S H cco I D.val ≤ E.val := by
    letI := ColourEq.lattice S H (i := ())
    have hjoin : ColourEq.join S H D.val.val K ≤ quotientPullback S H K E.val :=
      sup_le hdE (le_quotientPullback S H K E.val)
    intro q r hqr
    induction q using Quotient.inductionOn with | _ x =>
      induction r using Quotient.inductionOn with | _ y =>
        exact hjoin ((quotientColourEq_projection S H K _ _ x y).mp hqr)
  refine ⟨D,?_⟩
  apply le_antisymm ?_ hsurv
  by_contra hn
  have hlt : survivingEq S H cco I D.val < E.val := lt_of_le_of_ne hsurv (fun he => hn he.ge)
  exact (survivingEq_isDirection S H cco normalized I D.val D.property).1 (E.property.2 _ hlt)

/-- The quotient directions are EXACTLY the selected survivors, in both
logical directions and without a selected-direction oracle. -/
theorem selected_direction_iff (normalized : NoFiniteExactKernel S)
    (I : Set (Direction S))
    (E : ColourEq (actualQuotientSource S H (selectedHat S H cco I)) ()) :
    IsDirection _ E ↔ ∃ D : I, E = survivingEq S H cco I D.val := by
  constructor
  · intro h
    exact selected_direction_exhaustive S H cco normalized I ⟨E,h⟩
  · rintro ⟨D,rfl⟩
    exact survivingEq_isDirection S H cco normalized I D.val D.property

end CCO.MIGeometry
