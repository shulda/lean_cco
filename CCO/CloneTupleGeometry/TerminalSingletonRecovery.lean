import CCO.CloneTupleGeometry.TerminalStrongCoordinates
import CCO.TransitionClosure.OriginalTypedCylinderStrong

/-! Actual complete mixed spectra recover every original fine colour on
the terminal owner tuples. The proof includes repeated hidden coordinates:
the accepted mixed-cylinder equation uses their FULL semantic spectrum.
Equal visible tuples are separately read as equality via the clone marker,
and never as a new old diversity edge. -/

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 900000
universe u v w
namespace CCO.CloneTupleGeometry.OwnerStage
open ParityHasse.Original TransitionClosure TerminalLattice
noncomputable section
variable (B : OwnerStage.{u,v,w})

def tuplePairSpectrum {i j : B.Sorts}
    (q : FullCloneMITuple B.source i) (r : FullCloneMITuple B.source j) :
    (CloneSAP.source B.source).Menu i j :=
  {a | ∀ J : FullCloneProperMI B.source i, ∀ L : FullCloneProperMI B.source j,
    a ∈ originalTypedQuotientPairSpectrum (CloneSAP.source B.source) J.val L.val (q J) (r L)}

/-- Complete singleton formula for actual distinct clone representatives,
with no condition requiring their quotient coordinates to differ. -/
theorem terminal_clone_pair_singleton (ht : B.Terminal) {i j : B.Sorts}
    (x : CloneSAP.Carrier B.Point i) (y : CloneSAP.Carrier B.Point j)
    (a : (CloneSAP.source B.source).Atom i j)
    (hxy : (CloneSAP.source B.source).atomRel a x y) :
    B.tuplePairSpectrum (fullCloneMITuple B.source i x) (fullCloneMITuple B.source j y) = {a} := by
  have hc (J : FullCloneProperMI B.source i) (L : FullCloneProperMI B.source j) :=
    originalTypedCylinder_both_nonzero (CloneSAP.source B.source)
      (CloneSAP.homogeneous B.source B.homogeneous) (CloneSAP.strong_amalgamation B.source B.ap) J.val L.val
      (lt_of_le_of_ne bot_le (Ne.symm J.property.1))
      (lt_of_le_of_ne bot_le (Ne.symm L.property.1)) a x y hxy
  calc
    _ = {b | ∀ J : FullCloneProperMI B.source i, ∀ L : FullCloneProperMI B.source j,
      b ∈ (CloneSAP.source B.source).product
        (originalEquivDiversityPalette (CloneSAP.source B.source) J.val)
        ((CloneSAP.source B.source).product {a}
          (originalEquivDiversityPalette (CloneSAP.source B.source) L.val))} := by
      ext b
      constructor
      · intro hb J L
        rw [← hc J L]
        exact hb J L
      · intro hb J L
        change b ∈ originalTypedQuotientPairSpectrum (CloneSAP.source B.source) J.val L.val ⟦x⟧ ⟦y⟧
        rw [hc J L]
        exact hb J L
    _ = {a} := B.terminal_strong_cylinder_singleton ht a

/-- The selected singleton fine-colour recovery theorem at the genuine
terminal source. Original fine atoms retain their literal old names. -/
theorem terminal_original_pair_singleton (ht : B.Terminal) {i j : B.Sorts}
    (q : B.Point i) (r : B.Point j) (a : B.source.Atom i j)
    (hqr : B.source.atomRel a q r) :
    B.tuplePairSpectrum (originalOwnerMITuple B.source i q)
      (originalOwnerMITuple B.source j r) = {Sum.inl a} :=
  B.terminal_clone_pair_singleton ht (q,0) (r,0) (Sum.inl a)
    ((CloneSAP.colour_old_iff B.source (q,0) (r,0) a).mpr hqr)

/-- Visible equality uses TWO DISTINCT clones of the same owner. The
singleton is c, which is interpreted as visible equality and not as an
old source diversity atom. Hidden repeated-coordinate cases remain valid. -/
theorem terminal_equal_owner_singleton (ht : B.Terminal) {i : B.Sorts}
    (q : B.Point i) :
    B.tuplePairSpectrum (originalOwnerMITuple B.source i q)
      (originalOwnerMITuple B.source i q) = {Sum.inr ⟨rfl⟩} := by
  have hc := B.terminal_clone_pair_singleton ht (q,0) (q,1) (Sum.inr ⟨rfl⟩)
    ((CloneSAP.source_clone_iff B.source (q,0) (q,1)).mpr ⟨rfl,Nat.zero_ne_one⟩)
  rw [← originalOwnerMITuple_eq_clone B.source i q 0,
    ← originalOwnerMITuple_eq_clone B.source i q 1] at hc
  exact hc

end
end CCO.CloneTupleGeometry.OwnerStage
