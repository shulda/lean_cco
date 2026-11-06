import CCO.ExactEPGeometry.OriginalRetainedGlobalCorrectedMark
import CCO.ExactEPGeometry.OriginalRetainedSelectedOldMarkMask

/-!
# B062 C96/C103: the descended corrected mark satisfies the actual phase

The full global character masks, on ALL actual reached selected objects
and all their arrows, hold for the genuine descended original marking.
Every selected active point is represented at its true reached occupancy
anchor; inactive points have exactly the prescribed zero mark.
-/

universe u v w t
namespace CCO.ExactEPGeometry
open APCharacter APCharacter.SourceAge APCharacter.Towers RigidGroupoid.Geometry
noncomputable section

variable (A B : CurrentSource.{u,v,w,t})
variable (P : UnaryReduct A.source B.source)
variable (transport : ExactTraceTransport A.source B.source P)
variable (tp : ExactTraceProduct A.source B.source P)
variable (hOne : ∀ i j : A.Sorts, i = j)
variable {r : B.Sorts} (Kroot : Kernel B.source r)
variable (phase : SourcePhase B.source B.homogeneous
  (exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco) Kroot)
variable (E : ExactEq A.source (P.parent r))
variable (hE : E ≤ PrefixExactLargestLift.largest A B P transport tp r
  (current_kernel_exact_eq B Kroot))

/-- Every actual active selected point admits its genuine old reached
occupancy anchor as owner, with the SAME actual selected quotient point. -/
theorem originalRetainedSelectedActivePoint_on_anchor :
    let base := P.parent r
    let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
    let Q := originalExactSelectedQuotientCurrentSource A B P transport base hBase E
    let KQ := originalRetainedSelectedKernel A B P transport tp hOne Kroot E hE (Reached.root Kroot)
    let anchor := originalReachedOccupancyAnchor A B P base hBase E Kroot
    ∀ q : Sigma Q.Point, Nonempty (Bridge Q.source KQ q.1) →
      ∃ (c : OriginalReachedOccupancy A B P base hBase E Kroot)
        (x : Q.Point (Quotient.mk'' (anchor c).val)),
        (⟨Quotient.mk'' (anchor c).val,x⟩ : Sigma Q.Point) = q := by
  dsimp only
  intro q hq
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let Q := originalExactSelectedQuotientCurrentSource A B P transport base hBase E
  let KQ := originalRetainedSelectedKernel A B P transport tp hOne Kroot E hE (Reached.root Kroot)
  let anchor := originalReachedOccupancyAnchor A B P base hBase E Kroot
  let e := originalRetainedOccupancySelectedReachedEquiv A B P transport tp hOne Kroot E hE
  let b : Reached Q.source KQ := ⟨q.1,hq⟩
  let c := e.symm b
  have hn : (Quotient.mk'' (anchor c).val : Q.Sorts) = q.1 :=
    congrArg Subtype.val (e.apply_symm_apply b)
  refine ⟨c,?_⟩
  rcases q with ⟨j,x⟩
  dsimp only at hn
  exact ⟨hn.symm ▸ x,Sigma.ext hn (eqRec_heq hn.symm x)⟩

/-- At each real reached anchor the descended corrected bit is exactly
the canonical original mark of its precise old E-class representative. -/
theorem originalRetainedSelectedCorrectedMark_at_anchor :
    let base := P.parent r
    let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
    let Q := originalExactSelectedQuotientCurrentSource A B P transport base hBase E
    let anchor := originalReachedOccupancyAnchor A B P base hBase E Kroot
    ∀ (c : OriginalReachedOccupancy A B P base hBase E Kroot)
      (x : Q.Point (Quotient.mk'' (anchor c).val)),
      originalRetainedSelectedCorrectedMark A B P transport tp hOne Kroot phase E hE
        ⟨Quotient.mk'' (anchor c).val,x⟩ =
      UnarySource.mark (SingleStep.identification B phase)
        ⟨(anchor c).val,originalSelectedReachedEclassRepresentative
          A B P transport hOne Kroot E (anchor c) x⟩ := by
  dsimp only
  intro c x
  let a := originalReachedOccupancyAnchor A B P (P.parent r)
    (fun i => hOne (P.parent r) i) E Kroot c
  let p : Sigma B.Point := ⟨a.val,originalSelectedReachedEclassRepresentative
    A B P transport hOne Kroot E a x⟩
  have h := originalRetainedSelectedCorrectedMark_project A B P transport tp hOne Kroot phase E hE p
  rw [originalSelectedReachedRepresentative_total_spec] at h
  change _ = UnarySource.mark (SingleStep.identification B phase) p
  exact h.trans (by
    change UnarySource.mark (SingleStep.identification B phase) p + _ = _
    rw [originalRetainedNamedOffset_anchor_zero A B P transport tp hOne Kroot phase E hE c,add_zero])

/-- Genuine global legality for the ACTUAL retained selected phase,
proved from original canonical marking legality and complete arrow masks. -/
theorem originalRetainedSelectedCorrectedMark_globalMarking :
    (originalRetainedActualSelectedPhase A B P transport tp hOne Kroot phase E hE).masks.GlobalMarking
      (originalRetainedSelectedCorrectedMark A B P transport tp hOne Kroot phase E hE) := by
  classical
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let Q := originalExactSelectedQuotientCurrentSource A B P transport base hBase E
  let KQ := originalRetainedSelectedKernel A B P transport tp hOne Kroot E hE (Reached.root Kroot)
  let φ := originalRetainedActualSelectedPhase A B P transport tp hOne Kroot phase E hE
  let ζ := originalRetainedSelectedCorrectedMark A B P transport tp hOne Kroot phase E hE
  let mark := UnarySource.mark (SingleStep.identification B phase)
  have hMark : phase.masks.GlobalMarking mark := UnarySource.global_marking _
  have hValid (q : Sigma Q.Point) : φ.validBit q.1 (ζ q) := by
    intro hn
    let p := originalSelectedTaggedRepresentative A B P transport base hBase E q
    have hp : (Quotient.mk'' p.1 : Q.Sorts) = q.1 :=
      originalOccupancyRepresentative_class A B P base hBase E q.1
    have hi : ¬Nonempty (Bridge B.source Kroot p.1) := by
      intro h
      apply hn
      rw [← hp]
      exact (originalRetainedSelectedReached_iff A B P transport tp hOne Kroot E hE p.1).mpr h
    change originalRetainedCorrectedMark A B P transport tp hOne Kroot phase E hE p = 0
    change mark p + _ = 0
    rw [hMark.1 p hi,originalRetainedNamedOffset_inactive A B P transport tp hOne Kroot phase E hE p.1 hi,zero_add]
  refine ⟨hValid,?_⟩
  intro q s
  by_cases hq : Nonempty (Bridge Q.source KQ q.1)
  · by_cases hs : Nonempty (Bridge Q.source KQ s.1)
    · obtain ⟨c,x,hx⟩ := originalRetainedSelectedActivePoint_on_anchor A B P transport tp hOne Kroot E hE q hq
      obtain ⟨d,y,hy⟩ := originalRetainedSelectedActivePoint_on_anchor A B P transport tp hOne Kroot E hE s hs
      rw [← hx,← hy]
      rw [originalRetainedSelectedCorrectedMark_at_anchor A B P transport tp hOne Kroot phase E hE c x,
        originalRetainedSelectedCorrectedMark_at_anchor A B P transport tp hOne Kroot phase E hE d y]
      apply (originalRetainedActualSelectedPhase_masks_iff A B P transport tp hOne Kroot phase E hE c d _ _ _).mpr
      have h := originalRetainedSelectedOldGlobalMark_atomicMask A B P transport tp hOne Kroot phase E hE
        mark hMark c d
        (originalSelectedReachedEclassRepresentative A B P transport hOne Kroot E
          (originalReachedOccupancyAnchor A B P base hBase E Kroot c) x)
        (originalSelectedReachedEclassRepresentative A B P transport hOne Kroot E
          (originalReachedOccupancyAnchor A B P base hBase E Kroot d) y)
      rw [originalSelectedReachedEclassRepresentative_spec,originalSelectedReachedEclassRepresentative_spec] at h
      exact h
    · exact φ.inactive_masks_full _ _ (hValid q) (hValid s) (Or.inr hs) _
  · exact φ.inactive_masks_full _ _ (hValid q) (hValid s) (Or.inl hq) _

end
end CCO.ExactEPGeometry
