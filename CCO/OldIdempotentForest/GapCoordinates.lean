import CCO.GuardedOldSeams.EnvelopeMI
import CCO.TransitionClosure.OriginalNamedHiddenCoordinates

/-! B058 C08/C16: the actual exact-MI / FULL / named-coordinate bridge.

The literal original word square first gives FULL RAW exactness. The
terminal all-invariant-word theorem then identifies the represented exact
lattice with the FULL original invariant lattice. Only after those two
discharges can an exact-lattice MI be used as an existing named coordinate.
The reconstruction includes the ordinary empty-family Top convention.
-/

universe u v w t
namespace CCO.OldIdempotentForest

open CCO.ParityHasse.Original CCO.QuotientTransport CCO.TransitionClosure
open CCO.GuardedOldSeams CCO.RealClosure.Bounds CCO.ExactCRT

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S)
variable (nr2 : Selectors.OriginalNR2 S)
variable (cco : SemanticCCO.{u,v,max u v,w} S)
include H sap nr2 cco

/-- An ACTUAL represented exact MI above the direct original-word
envelope has the SAME underlying setoid as one existing nonzero proper
FULL named coordinate. Neither naming nor all-invariant exactness is a
provider premise: terminal original NR2 proves the required identification. -/
theorem gap_exactMI_named {a : ι} (W : PositiveWord S a a)
    (idem : S.product (PositiveWord.profile S W) (PositiveWord.profile S W) =
      PositiveWord.profile S W)
    (J : ExactEq S H cco a)
    (above : (⟨(envelope S (PositiveWord.profile S W) idem).val,
      envelope_raw_exact S H sap W idem⟩ : ExactEq S H cco a) ≤ J)
    (hJ : InfIrred J) :
    ∃ D : OriginalNamedHiddenCoordinate S H a,
      D.val.val = J.val ∧ envelope S (PositiveWord.profile S W) idem ≤ D.val := by
  let exactFull : ColourEq S a ≃o ExactEq S H cco a :=
    terminalExactOrderIso S H cco (sortNR2_of_originalNR2 S H nr2)
  let full : ColourEq S a := exactFull.symm J
  let Φ : ExactEq S H cco a ≃o InvEq G (X a) :=
    exactFull.symm.trans (originalFullColourEqInvEqOrderIso S H)
  have hProperExact :=
    (CCO.RealClosure.SAP.FiniteLattice.proper_mi_iff J).mp hJ
  have hProperFull : ProperMeetIrreducible (originalColourEqAsInvEq S H full) := by
    change ProperMeetIrreducible (Φ J)
    constructor
    · intro htop
      apply hProperExact.1
      apply Φ.injective
      exact htop.trans Φ.map_top.symm
    · intro L N hLN
      have hPull : Φ.symm L ⊓ Φ.symm N = J := by
        apply Φ.injective
        rw [Φ.map_inf,Φ.apply_symm_apply,Φ.apply_symm_apply]
        exact hLN.symm
      rcases hProperExact.2 (Φ.symm L) (Φ.symm N) hPull with hL | hN
      · exact Or.inl (by
          simpa only [OrderIso.apply_symm_apply] using (congrArg Φ hL).symm)
      · exact Or.inr (by
          simpa only [OrderIso.apply_symm_apply] using (congrArg Φ hN).symm)
  have hEnvelopeFull : envelope S (PositiveWord.profile S W) idem ≤ full := by
    intro x y hxy
    exact above hxy
  have hFullNonzero : (⊥ : ColourEq S a) < full :=
    lt_of_lt_of_le
      (envelope_gt_bot S (PositiveWord.profile S W) idem
        (PositiveWord.profile_nonempty_of_SAP S H sap W)) hEnvelopeFull
  let D := original_full_MI_named_hidden_of_terminalNR2
    S H nr2 full hFullNonzero hProperFull
  refine ⟨D,?_,hEnvelopeFull⟩
  rfl

/-- The full exact original-word envelope is reconstructed by ALL of its
existing named FULL proper coordinates. The reverse implication uses
the represented exact-MI theorem only AFTER `envelope_raw_exact`, and the
preceding terminal bridge supplies EVERY one of its exact-MI coordinates.
If there are no such coordinates, this is the literal universal relation. -/
theorem gap_envelope_iff_named_coordinates {a : ι} (W : PositiveWord S a a)
    (idem : S.product (PositiveWord.profile S W) (PositiveWord.profile S W) =
      PositiveWord.profile S W) (x y : X a) :
    envelope S (PositiveWord.profile S W) idem x y ↔
      ∀ D : OriginalNamedHiddenCoordinate S H a,
        envelope S (PositiveWord.profile S W) idem ≤ D.val → D.val x y := by
  constructor
  · intro hxy D above
    exact above hxy
  · intro hNamed
    apply (envelope_mi_pointwise S H sap cco W idem x y).mpr
    intro J above hJ
    have hAbove : (⟨(envelope S (PositiveWord.profile S W) idem).val,
        envelope_raw_exact S H sap W idem⟩ : ExactEq S H cco a) ≤ J := by
      intro p q hpq
      exact above p q hpq
    obtain ⟨D,hD,hEnvelopeD⟩ := gap_exactMI_named S H sap nr2 cco W idem J hAbove hJ
    have hxy := hNamed D hEnvelopeD
    rw [← hD]
    exact hxy

/-- The missing-coordinate boundary is genuinely Top, not a missing
certificate: the empty family of named proper coordinates has universal
same-sort relation as its intersection. -/
theorem gap_envelope_eq_top_of_no_named {a : ι} (W : PositiveWord S a a)
    (idem : S.product (PositiveWord.profile S W) (PositiveWord.profile S W) =
      PositiveWord.profile S W)
    (none : ∀ D : OriginalNamedHiddenCoordinate S H a,
      ¬ envelope S (PositiveWord.profile S W) idem ≤ D.val) :
    envelope S (PositiveWord.profile S W) idem = (⊤ : ColourEq S a) := by
  apply ColourEq.ext
  intro x y
  constructor
  · intro _
    trivial
  · intro _
    apply (gap_envelope_iff_named_coordinates S H sap nr2 cco W idem x y).mpr
    intro D above
    exact False.elim (none D above)

end CCO.OldIdempotentForest
