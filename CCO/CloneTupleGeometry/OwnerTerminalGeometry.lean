import CCO.CloneTupleGeometry.OwnerSafeTower
import CCO.CloneTupleGeometry.FullKernelMI
import CCO.RealClosure.Bounds.TerminalLattice
import CCO.TerminalPowers.WholeSource

/-! Source instances at the actual safe tower endpoint. Terminality concerns
the FULL original colour-invariant lattice, and whole-source homogeneity
identifies it with all full-automorphism invariant equivalences. Every such
equivalence has a genuine RAW word. The clone kernel is nonzero and proper,
so the fixed finite family of proper MI coordinates is nonempty. -/

universe u v w
namespace CCO.CloneTupleGeometry.OwnerStage
open APCharacter APCharacter.Towers ParityHasse.Original
open RigidGroupoid.Geometry TerminalPowers RealClosure.Bounds
noncomputable section
variable (B : OwnerStage.{u,v,w})

/-- Actual terminality excludes finite intervals for arbitrary FULL
current equivalences, including those not initially presented by words. -/
theorem terminal_interval_infinite (ht : B.Terminal) {i : B.Sorts}
    (E F : ColourEq (CloneSAP.source B.source) i) (hEF : E < F)
    (a : CloneSAP.Carrier B.Point i) : Infinite (RelativeClass E.val F.val a) :=
  B.cloneSafeCurrent.terminal_interval_infinite ht E F hEF a

/-- Numerical FULL NR2 is derived from the actual tower endpoint; it is
not a supplied represented-sublattice or finite-source hypothesis. -/
theorem terminal_sortNR2 (ht : B.Terminal) (i : B.Sorts) :
    SortNR2 (CloneSAP.source B.source) i := by
  intro E F hEF a htwo
  by_cases he : E = F
  · subst F
    have hone := relativeIndex_self E.val a
    exact (by decide : (1 : ℕ) ≠ 2) (hone.symm.trans htwo)
  · have hpos : 0 < Nat.card (RelativeClass E.val F.val a) := by
      change 0 < relativeIndex E.val F.val a
      rw [htwo]
      decide
    have hfinite := (Nat.card_pos_iff.mp hpos).2
    exact ht ⟨i,E,F,a,lt_of_le_of_ne hEF he,hfinite⟩

/-- Arbitrary whole-source full-automorphism invariant setoids, not just
named equivalences, satisfy terminal NR2. -/
theorem terminal_fullSortNR2 (ht : B.Terminal) (i : B.Sorts) :
    FullSortNR2 (CloneSAP.source B.source) i :=
  (fullSortNR2_iff (CloneSAP.source B.source) B.cloneCurrent.homogeneous i).mpr
    (B.terminal_sortNR2 ht i)

/-- The actual terminal clone discharges the RAW presentation provider
for every FULL invariant equivalence on every final named sort. -/
theorem terminal_all_equivalences_exact (ht : B.Terminal) {i : B.Sorts}
    (E : ColourEq (CloneSAP.source B.source) i) :
    ExactCRT.IsExactEq (CloneSAP.source B.source) E.val :=
  terminal_all_exact (CloneSAP.source B.source) B.cloneCurrent.homogeneous
    (B.terminal_sortNR2 ht i) E

/-- Infinite OWNER types make K proper; infinite clone fibres alone would
only prove its nonzeroness. -/
theorem clone_kernel_ne_top (i : B.Sorts) : fullCloneKernel B.source i ≠ ⊤ := by
  letI := B.infinite i
  obtain ⟨x,y,hxy⟩ := exists_pair_ne (B.Point i)
  intro he
  have hk : fullCloneKernel B.source i (x,0) (y,0) := by
    rw [he]
    trivial
  exact hxy hk

/-- A final owner sort has at least one actual proper nonidentity FULL
MI coordinate. Thus its visible tuple never has an empty coordinate list. -/
theorem clone_MI_nonempty (i : B.Sorts) : Nonempty (FullCloneProperMI B.source i) := by
  have hnot : ¬(⊤ : ColourEq (CloneSAP.source B.source) i) ≤ fullCloneKernel B.source i := by
    intro h
    exact B.clone_kernel_ne_top i (top_le_iff.mp h)
  obtain ⟨J,_,_⟩ := fullCloneKernel_mi_separates B.source i ⊤ hnot
  exact ⟨J⟩

/-- All selected FULL MI coordinate kernels have actual terminal RAW
presentations, discharged on this new SAP+HOM CCO clone source. -/
theorem terminal_MI_exact (ht : B.Terminal) (i : B.Sorts)
    (J : FullCloneProperMI B.source i) :
    ExactCRT.IsExactEq (CloneSAP.source B.source) J.val.val :=
  B.terminal_all_equivalences_exact ht J.val

end
end CCO.CloneTupleGeometry.OwnerStage
