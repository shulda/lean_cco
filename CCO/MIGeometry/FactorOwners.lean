import CCO.MIGeometry.SurvivingDirections
import CCO.MIGeometry.UnaryFactors
import CCO.AclOwners.HarmlessFullAut

/-! Canonical complementary factors and harmlessness IN EACH actual
quotient. Original harmlessness alone is not used as a substitute. -/
universe v w t
namespace CCO.MIGeometry
open ParityHasse.Original RealClosure.Bounds
open FinitePackets.Geometry FinitePackets.Normalization RawExact AclOwners
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] (cco : SemanticCCO.{0,v,0,w} S)

theorem selectedQuotient_infinite (normalized : NoFiniteExactKernel S)
    (I : Set (Direction S)) (hne : I.Nonempty) :
    Infinite (Quotient (selectedHat S H cco I).val) := by
  obtain ⟨D,hD⟩ := hne
  apply not_finite_iff_infinite.mp
  intro hf
  letI := hf
  apply (survivingEq_isDirection S H cco normalized I D hD).1
  intro x
  exact Finite.of_injective Subtype.val Subtype.val_injective

/-- The actual selected quotient criterion is discharged using the FULL
list of its minimal infinite directions. The owner J need not be exact. -/
theorem selected_owner_harmless (normalized : NoFiniteExactKernel S)
    (I : Set (Direction S)) (hne : I.Nonempty) (J : ColourEq S ())
    (hKJ : selectedHat S H cco I ≤ J) (hDJ : ∀ D ∈ I, D.val ≤ J) :
    FullHarmless (actualQuotientSource S H (selectedHat S H cco I))
      (quotientColourEq S H (selectedHat S H cco I) J hKJ) := by
  classical
  let K := selectedHat S H cco I
  let B := selectedPresentation S H cco I
  have hB := selectedPresentation_represents S H cco I
  letI := originalQuotientAction S H K
  letI := selectedQuotient_infinite S H cco normalized I hne
  let T := actualQuotientSource S H K
  let qH := actualQuotient_homogeneous S H K B hB cco
  let qCCO : SemanticCCO.{0,v,0,v} T := actualQuotient_CCO S H K B hB cco
  apply (full_harmless_iff_containsDirections T qH qCCO _).mpr
  intro E
  obtain ⟨D,hD⟩ := selected_direction_exhaustive S H cco normalized I E
  rw [hD]
  letI := ColourEq.lattice S H (i := ())
  have hjoin : ColourEq.join S H D.val.val K ≤ J := sup_le (hDJ D.val D.property) hKJ
  intro q r hqr
  induction q using Quotient.inductionOn with | _ x =>
    induction r using Quotient.inductionOn with | _ y =>
      apply (quotientColourEq_projection S H K J hKJ x y).mpr
      exact hjoin ((quotientColourEq_projection S H K _ _ x y).mp hqr)

noncomputable def complementaryCore (D : Direction S) : ColourEq S () :=
  selectedHat S H cco {E | E ≠ D}

noncomputable def factorOwner (D : Direction S) : ColourEq S () :=
  ColourEq.join S H (hat S H cco D) (complementaryCore S H cco D)

theorem complementaryCore_exact (D : Direction S) :
    ExactCRT.IsExactEq S (i := ()) (complementaryCore S H cco D).val :=
  selectedHat_exact S H cco _

theorem factorOwner_exact (D : Direction S) :
    ExactCRT.IsExactEq S (i := ()) (factorOwner S H cco D).val :=
  ExactCRT.isExactEq_sup S H (semanticCCO_change_universe S cco)
    (hat_exact S H cco D) (complementaryCore_exact S H cco D)

theorem hat_inf_complementary (normalized : NoFiniteExactKernel S) (D : Direction S) :
    hat S H cco D ⊓ complementaryCore S H cco D = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro x y hxy
  have hall : allHat S H cco x y := by
    intro E
    by_cases he : E = D
    · cases he
      exact hxy.1
    · exact hxy.2 ⟨E,he⟩
  rwa [allHat_eq_bot S H cco normalized] at hall

theorem direction_le_complementary (normalized : NoFiniteExactKernel S) (D : Direction S) :
    D.val ≤ complementaryCore S H cco D := by
  intro x y hxy E
  exact direction_le_hat_other S H cco normalized E.val D E.property hxy

theorem all_directions_le_factorOwner (normalized : NoFiniteExactKernel S)
    (D E : Direction S) : E.val ≤ factorOwner S H cco D := by
  letI := ColourEq.lattice S H (i := ())
  by_cases he : E = D
  · subst E
    exact (direction_le_complementary S H cco normalized D).trans le_sup_right
  · exact (direction_le_hat_other S H cco normalized D E (Ne.symm he)).trans le_sup_left

@[simp] theorem selectedHat_singleton (D : Direction S) :
    selectedHat S H cco {D} = hat S H cco D := by
  apply ColourEq.ext
  intro x y
  constructor
  · intro h
    exact h ⟨D,Set.mem_singleton D⟩
  · intro h E
    have he : E.val = D := E.property
    cases E with
    | mk E hE =>
      change E = D at hE
      subst E
      exact h

/-- Actual recipient-factor harmlessness; its only minimal infinite
direction is supplied by the proved selected-quotient classification. -/
theorem factor_recipient_harmless (normalized : NoFiniteExactKernel S) (D : Direction S) :
    FullHarmless (actualQuotientSource S H (hat S H cco D))
      (quotientColourEq S H (hat S H cco D) (factorOwner S H cco D)
        (by letI := ColourEq.lattice S H (i := ()); exact le_sup_left)) := by
  letI := ColourEq.lattice S H (i := ())
  have transfer (K : ColourEq S ()) (he : selectedHat S H cco {D} = K)
      (hKJ : K ≤ factorOwner S H cco D) :
      FullHarmless (actualQuotientSource S H K)
        (quotientColourEq S H K (factorOwner S H cco D) hKJ) := by
    subst K
    exact selected_owner_harmless S H cco normalized {D} (Set.singleton_nonempty D)
      (factorOwner S H cco D) hKJ
      (fun E _ => all_directions_le_factorOwner S H cco normalized D E)
  exact transfer _ (selectedHat_singleton S H cco D) le_sup_left

/-- The OPPOSITE factor is checked independently against ALL of its
surviving directions. It is not inferred from original harmlessness. -/
theorem factor_opposite_harmless (normalized : NoFiniteExactKernel S)
    (h : 2 ≤ directionCount S) (D : Direction S) :
    FullHarmless (actualQuotientSource S H (complementaryCore S H cco D))
      (quotientColourEq S H (complementaryCore S H cco D) (factorOwner S H cco D)
        (by letI := ColourEq.lattice S H (i := ()); exact le_sup_right)) := by
  letI := ColourEq.lattice S H (i := ())
  obtain ⟨E,hE⟩ := exists_other_direction S h D
  exact selected_owner_harmless S H cco normalized {E | E ≠ D} ⟨E,hE.symm⟩
    (factorOwner S H cco D) le_sup_right
    (fun E _ => all_directions_le_factorOwner S H cco normalized D E)

end CCO.MIGeometry
