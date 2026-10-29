import CCO.MIGeometry.Pseudocomplements
import CCO.MIGeometry.QuotientExact

/-! Every selected maximal-core quotient is normalized. The proof uses
finite relative classes, not division of infinite cardinalities. -/
universe v w t
namespace CCO.MIGeometry
open ParityHasse.Original RealClosure.Bounds
open FinitePackets.Geometry FinitePackets.Normalization RawExact AclOwners
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] (cco : SemanticCCO.{0,v,0,w} S)

noncomputable def selectedHat (I : Set (Direction S)) : ColourEq S () :=
  colourFamilyMeet S (fun d : I => hat S H cco d.val)

theorem selectedHat_exact (I : Set (Direction S)) :
    ExactCRT.IsExactEq S (i := ()) (selectedHat S H cco I).val :=
  colourFamilyMeet_exact S _ (fun d => hat_exact S H cco d.val)

theorem selectedHat_le (I : Set (Direction S)) (D : Direction S) (hD : D ∈ I) :
    selectedHat S H cco I ≤ hat S H cco D := fun _ _ h => h ⟨D,hD⟩

theorem direction_inf_selectedHat (normalized : NoFiniteExactKernel S)
    (I : Set (Direction S)) (D : Direction S) (hD : D ∈ I) :
    D.val ⊓ selectedHat S H cco I = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro x y hxy
  have hh : (hat S H cco D ⊓ D.val) x y :=
    ⟨selectedHat_le S H cco I D hD hxy.2,hxy.1⟩
  rwa [hat_disjoint S H cco normalized D] at hh

/-- An exact original finite-index extension of a selected core meet
collapses. Restriction of the relative classes is the class injection in
C04, already proved generically in the finite-index foundation. -/
theorem selectedHat_finite_exact_extension (normalized : NoFiniteExactKernel S)
    (I : Set (Direction S)) (E : ColourEq S ())
    (hE : ExactCRT.IsExactEq S (i := ()) E.val)
    (hKE : selectedHat S H cco I ≤ E)
    (hfin : FiniteIndex S (selectedHat S H cco I) E) :
    E = selectedHat S H cco I := by
  apply le_antisymm ?_ hKE
  intro x y hxy d
  apply (le_hat_iff S H cco normalized d.val E hE).mpr ?_ hxy
  have hr := finiteIndex_restrict S d.val.val (selectedHat S H cco I) E hfin
  rw [direction_inf_selectedHat S H cco normalized I d.val d.property] at hr
  have hz := normalized_exact_finite S normalized (d.val.val ⊓ E)
    (ExactCRT.isExactEq_inf S (direction_exact S H cco d.val) hE)
    ((finiteIndex_bottom_iff_finite_classes S _).mp hr)
  rwa [inf_comm]

/-- No nonidentity finite exact equivalence appears in ANY selected
quotient. In particular this holds for every nonempty selected I. -/
theorem selectedQuotient_normalized (normalized : NoFiniteExactKernel S)
    (I : Set (Direction S)) :
    NoFiniteExactKernel (actualQuotientSource S H (selectedHat S H cco I)) := by
  intro E hfin D hD
  let K := selectedHat S H cco I
  let B := ExactCRT.exactPresentation S (selectedHat_exact S H cco I)
  have hB : evaluate S B.words = K.val.r :=
    ExactCRT.exactPresentation_represents S (selectedHat_exact S H cco I)
  have hE := quotientPullback_exact S H cco K B hB E ⟨D,hD⟩
  have heq : quotientColourEq S H K (quotientPullback S H K E)
      (le_quotientPullback S H K E) = E :=
    (quotientColourInterval S H K).apply_symm_apply E
  have hrel : FiniteIndex S K (quotientPullback S H K E) := by
    apply (quotient_finiteClasses_iff S H K _ _).mp
    rw [heq]
    exact (finiteIndex_bottom_iff_finite_classes _ E).mp hfin
  have hp := selectedHat_finite_exact_extension S H cco normalized I
    (quotientPullback S H K E) hE (le_quotientPullback S H K E) hrel
  apply ColourEq.ext
  intro q r
  induction q using Quotient.inductionOn with | _ x =>
    induction r using Quotient.inductionOn with | _ y =>
      change quotientPullback S H K E x y ↔ Quotient.mk'' x = Quotient.mk'' y
      rw [hp]
      exact Quotient.eq.symm

end CCO.MIGeometry
