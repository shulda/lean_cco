import CCO.ExactEPGeometry.OriginalRetainedSelectedOldMarkMask
import CCO.ExactEPGeometry.OriginalSelectedFiniteOrbitalOldMark

/-!
# B062 C88–C96: finite ACTUAL active quotient diagrams, both mask directions

Fix arbitrary finitely many already existing selected-quotient E-classes,
each indexed by a genuine reached original E-occupancy component. The
full locally legal C84 quotient atomic masks are equivalent to the
existence of ONE globally legal marking on the ACTUAL old SourcePhase
having exactly the prescribed bits on the chosen old E-representatives.

The forward direction is the actual C91–C94 selected-character seed
extension, source marking pullback and zero gauge at canonical anchors.
The reverse direction is new: every old globally legal marking obeys
the quotient masks of EVERY selected whole full-exact Arrow. The source
C83 pair relation equivalence, the C84 exact character, and the
literal selected E-class representatives justify that implication.

This is an exact, unconditional equivalence for arbitrary FINITE
configurations of already realized ACTIVE selected quotient points.
It does not assume a hypothetical quotient SAP, replace the entire
unmarked quotient-age induction by this realized-point statement,
or silently include the inactive sorts and full successor quotient
tower, which remain separate C95–C105 tasks.
-/

universe u v w t z

namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.Towers
open RigidGroupoid.Geometry
open CCO.RigidGroupoid.Phase
open CategoryTheory

noncomputable section

/-- On ANY finite set of actual selected quotient active points, full
orbital character-mask legality is EQUIVALENT to realization of
all chosen bits by ONE global source-legal old marking. This
also covers duplicate projected K/E gate classes: their character-zero
identity makes inconsistent prescriptions impossible. -/
theorem originalRetainedSelectedFiniteActiveMasks_iff_oldGlobalMark
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
      (current_kernel_exact_eq B Kroot)) :
    let Occ := OriginalReachedOccupancy A B P (P.parent r)
      (fun i => hOne (P.parent r) i) E Kroot
    letI := originalRetainedOccupancyGroupoid
      A B P transport tp hOne Kroot E hE
    let Q := originalExactSelectedQuotientCurrentSource
      A B P transport (P.parent r) (fun i => hOne (P.parent r) i) E
    let anchor := originalReachedOccupancyAnchor
      A B P (P.parent r) (fun i => hOne (P.parent r) i) E Kroot
    let K := fun o : Occ => originalRetainedSelectedKernel
      A B P transport tp hOne Kroot E hE (anchor o)
    let chi := originalRetainedSelectedOccupancyCharacter
      A B P transport tp hOne Kroot phase E hE
    ∀ {V : Type z} [Finite V]
      (owners : V → Occ)
      (point : ∀ v : V,
        Q.Point (Quotient.mk'' (anchor (owners v)).val))
      (bits : V → ZMod 2),
      (∀ i j : V,
        originalSelectedCompleteAtomicMask Q
          (K (owners i)) (K (owners j))
          (fun (R : owners i ⟶ owners j) => chi.value R)
          (Q.source.colour (point i) (point j))
          (bits i) (bits j)) ↔
      ∃ oldMark : Sigma B.Point → ZMod 2,
        phase.masks.GlobalMarking oldMark ∧
          ∀ v : V,
            oldMark ⟨(anchor (owners v)).val,
              originalSelectedReachedEclassRepresentative
                A B P transport hOne Kroot E
                (anchor (owners v)) (point v)⟩ = bits v := by
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let Qall : CurrentSource.{u,v,v,t} :=
    originalExactAllCurrentQuotientCurrentSource
      A B P transport base hBase E
  letI : ∀ i : Qall.Sorts, MulAction B.G (Qall.Point i) := Qall.action
  let SelOcc := OriginalOccupancy A B P base hBase E
  letI : Finite SelOcc := originalOccupancyFinite A B P base hBase E
  letI : Fintype SelOcc := Fintype.ofFinite SelOcc
  let sigma : SelOcc ↪ B.Sorts :=
    originalOccupancyRepresentativeEmbedding A B P base hBase E
  let D : SelectedRetyping (X := Qall.Point) sigma (G := B.G) :=
    originalSelectedSortRetyping A B P transport base hBase E
  let Occ := OriginalReachedOccupancy A B P base hBase E Kroot
  letI : Groupoid Occ :=
    originalRetainedOccupancyGroupoid
      A B P transport tp hOne Kroot E hE
  let Q := originalExactSelectedQuotientCurrentSource
    A B P transport base hBase E
  let anchor := originalReachedOccupancyAnchor
    A B P base hBase E Kroot
  let K := fun o : Occ => originalRetainedSelectedKernel
    A B P transport tp hOne Kroot E hE (anchor o)
  let chi := originalRetainedSelectedOccupancyCharacter
    A B P transport tp hOne Kroot phase E hE
  change ∀ {V : Type z} [Finite V]
      (owners : V → Occ)
      (point : ∀ v : V,
        Q.Point (Quotient.mk'' (anchor (owners v)).val))
      (bits : V → ZMod 2),
      (∀ i j : V,
        originalSelectedCompleteAtomicMask Q
          (K (owners i)) (K (owners j))
          (fun (R : owners i ⟶ owners j) => chi.value R)
          (Q.source.colour (point i) (point j))
          (bits i) (bits j)) ↔
      ∃ oldMark : Sigma B.Point → ZMod 2,
        phase.masks.GlobalMarking oldMark ∧
          ∀ v : V,
            oldMark ⟨(anchor (owners v)).val,
              originalSelectedReachedEclassRepresentative
                A B P transport hOne Kroot E
                (anchor (owners v)) (point v)⟩ = bits v
  intro V _ owners point bits
  constructor
  · intro hMasks
    exact originalRetainedSelectedFiniteOrbitalOldMark
      A B P transport tp hOne Kroot phase E hE
        owners point bits hMasks
  · rintro ⟨oldMark,hGlobal,hValues⟩ i j
    let a := anchor (owners i)
    let b := anchor (owners j)
    let x := originalSelectedReachedEclassRepresentative
      A B P transport hOne Kroot E a (point i)
    let y := originalSelectedReachedEclassRepresentative
      A B P transport hOne Kroot E b (point j)
    have hx : D.pointEquiv a.val (Quotient.mk'' x) = point i :=
      originalSelectedReachedEclassRepresentative_spec
        A B P transport hOne Kroot E a (point i)
    have hy : D.pointEquiv b.val (Quotient.mk'' y) = point j :=
      originalSelectedReachedEclassRepresentative_spec
        A B P transport hOne Kroot E b (point j)
    have hMasks := originalRetainedSelectedOldGlobalMark_atomicMask
      A B P transport tp hOne Kroot phase E hE
        oldMark hGlobal (owners i) (owners j) x y
    change originalSelectedCompleteAtomicMask Q
        (K (owners i)) (K (owners j))
        (fun (R : owners i ⟶ owners j) => chi.value R)
        (Q.source.colour
          (D.pointEquiv a.val (Quotient.mk'' x))
          (D.pointEquiv b.val (Quotient.mk'' y)))
        (oldMark ⟨a.val,x⟩) (oldMark ⟨b.val,y⟩)
      at hMasks
    rw [hx,hy,hValues i,hValues j] at hMasks
    exact hMasks

end
end CCO.ExactEPGeometry
