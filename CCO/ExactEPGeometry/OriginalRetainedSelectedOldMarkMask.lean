import CCO.ExactEPGeometry.OriginalRetainedSelectedArrowRealPair
import CCO.ExactEPGeometry.OriginalSelectedCompleteAtomicMask
import CCO.APCharacter.ActualMasks

/-!
# B062 C88/C96: true old globally legal markings satisfy selected atomic masks

The forward direction of C93 transports a full selected character marking
to an old source marking. For the reverse marked-age direction we need
more: ANY genuinely legal old SourcePhase marking must induce precisely
the full selected-quotient Arrow-character masks on its active occupancy
anchors. This must be verified on whole real quotient orbital colours,
including the complete gate identity (not just quotient equality).

Given a real selected pair represented at the two chosen old reached
anchors, take an arbitrary whole Arrow of the selected occupancy
groupoid containing the pair. The proved C83 Hom equivalence pulls it
back to ONE whole old Arrow; the genuine E-bisaturated pair-pullback
theorem proves it contains the actual old representatives. Therefore
the ORIGINAL phase mask forces the correct bit difference. At anchors
the selected C84 character is by definition the old full Arrow
character, with no artificially assumed or forgotten object gauge.

This is the local converse on ACTIVE already-represented pairs;
the inactive-sort part and the full quotient successor age/induction
still require separate source proofs.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.Towers
open RigidGroupoid.Geometry
open CCO.RigidGroupoid.Phase
open CategoryTheory

noncomputable section

/-- Every ACTUAL old globally legal SourcePhase marking gives legal
FULL-Arrow selected atomic masks on any two selected quotient E-classes
represented on genuine reached occupancy anchors. All possible
selected full Arrows are tested, not only one particular old lift. -/
theorem originalRetainedSelectedOldGlobalMark_atomicMask
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (hOne : ∀ i j : A.Sorts, i = j)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (phase : SourcePhase B.source B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) Kroot)
    (E : ExactEq A.source (P.parent r))
    (hE : E ≤ PrefixExactLargestLift.largest A B P transport tp r
      (current_kernel_exact_eq B Kroot))
    (mark : Sigma B.Point → ZMod 2)
    (hMark : phase.masks.GlobalMarking mark) :
    let base := P.parent r
    let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
    let Qall := originalExactAllCurrentQuotientCurrentSource
      A B P transport base hBase E
    letI : ∀ i : Qall.Sorts, MulAction B.G (Qall.Point i) := Qall.action
    let Occ := OriginalReachedOccupancy A B P base hBase E Kroot
    letI := originalRetainedOccupancyGroupoid
      A B P transport tp hOne Kroot E hE
    let D := originalSelectedSortRetyping A B P transport base hBase E
    let Q := originalExactSelectedQuotientCurrentSource
      A B P transport base hBase E
    let anchor := originalReachedOccupancyAnchor
      A B P base hBase E Kroot
    let K := fun o : Occ => originalRetainedSelectedKernel
      A B P transport tp hOne Kroot E hE (anchor o)
    let chi := originalRetainedSelectedOccupancyCharacter
      A B P transport tp hOne Kroot phase E hE
    ∀ (a b : Occ) (x : B.Point (anchor a).val)
      (y : B.Point (anchor b).val),
      originalSelectedCompleteAtomicMask Q (K a) (K b)
        (fun (T : a ⟶ b) => chi.value T)
        (Q.source.colour
          (D.pointEquiv (anchor a).val (Quotient.mk'' x))
          (D.pointEquiv (anchor b).val (Quotient.mk'' y)))
        (mark ⟨(anchor a).val,x⟩)
        (mark ⟨(anchor b).val,y⟩) := by
  let CB := exactCalculus_of_homogeneous_CCO
    B.source B.homogeneous B.cco
  letI : Groupoid (Reached B.source Kroot) :=
    Reached.groupoid B.homogeneous CB (A := Kroot)
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let Qall : CurrentSource.{u,v,v,t} :=
    originalExactAllCurrentQuotientCurrentSource
      A B P transport base hBase E
  letI : ∀ i : Qall.Sorts, MulAction B.G (Qall.Point i) := Qall.action
  let Occ := OriginalReachedOccupancy A B P base hBase E Kroot
  letI : Groupoid Occ :=
    originalRetainedOccupancyGroupoid
      A B P transport tp hOne Kroot E hE
  let SelOcc := OriginalOccupancy A B P base hBase E
  letI : Finite SelOcc := originalOccupancyFinite
    A B P base hBase E
  letI : Fintype SelOcc := Fintype.ofFinite SelOcc
  let sigma : SelOcc ↪ B.Sorts :=
    originalOccupancyRepresentativeEmbedding A B P base hBase E
  let D : SelectedRetyping (X := Qall.Point) sigma (G := B.G) :=
    originalSelectedSortRetyping A B P transport base hBase E
  let Q := originalExactSelectedQuotientCurrentSource
    A B P transport base hBase E
  let anchor := originalReachedOccupancyAnchor
    A B P base hBase E Kroot
  let K := fun o : Occ => originalRetainedSelectedKernel
    A B P transport tp hOne Kroot E hE (anchor o)
  let chi := originalRetainedSelectedOccupancyCharacter
    A B P transport tp hOne Kroot phase E hE
  change ∀ (a b : Occ) (x : B.Point (anchor a).val)
      (y : B.Point (anchor b).val),
      originalSelectedCompleteAtomicMask Q (K a) (K b)
        (fun (T : a ⟶ b) => chi.value T)
        (Q.source.colour
          (D.pointEquiv (anchor a).val (Quotient.mk'' x))
          (D.pointEquiv (anchor b).val (Quotient.mk'' y)))
        (mark ⟨(anchor a).val,x⟩)
        (mark ⟨(anchor b).val,y⟩)
  intro a b x y
  apply (originalSelectedCompleteAtomicMask_iff_at_pair
    Q (K a) (K b) (fun (T : a ⟶ b) => chi.value T)
      (D.pointEquiv (anchor a).val (Quotient.mk'' x))
      (D.pointEquiv (anchor b).val (Quotient.mk'' y))
      (mark ⟨(anchor a).val,x⟩)
      (mark ⟨(anchor b).val,y⟩)).2
  intro T hT
  let e := originalRetainedSelectedArrowEquiv
    A B P transport tp hOne Kroot E hE (anchor a) (anchor b)
  let R := e.symm T
  have hSelected : (e R).rel
      (D.pointEquiv (anchor a).val (Quotient.mk'' x))
      (D.pointEquiv (anchor b).val (Quotient.mk'' y)) := by
    have heq : e R = T := e.apply_symm_apply T
    rw [heq]
    exact hT
  have hOld : R.rel x y :=
    (originalRetainedSelectedArrow_real_pair_iff
      A B P transport tp hOne Kroot E hE
        (anchor a) (anchor b) R x y).mp hSelected
  have hAllowed : phase.allows (B.source.colour x y)
      (mark ⟨(anchor a).val,x⟩)
      (mark ⟨(anchor b).val,y⟩) :=
    hMark.2 (⟨(anchor a).val,x⟩ : Sigma B.Point)
      (⟨(anchor b).val,y⟩ : Sigma B.Point)
  have hBits := (phase.rigid_mask_iff
    (anchor a) (anchor b) R x y hOld
      (mark ⟨(anchor a).val,x⟩)
      (mark ⟨(anchor b).val,y⟩)).mp hAllowed
  change mark ⟨(anchor b).val,y⟩ =
    mark ⟨(anchor a).val,x⟩ + phase.character.value (e.symm T)
  exact hBits.2.2

end
end CCO.ExactEPGeometry
