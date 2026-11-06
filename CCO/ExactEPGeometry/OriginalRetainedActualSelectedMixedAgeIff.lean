import CCO.ExactEPGeometry.OriginalRetainedActualSelectedMasks
import CCO.ExactEPGeometry.OriginalRetainedMixedActualNextAgeIff

/-!
# B062 C96/C103: actual SourcePhase mixed finite age

The concrete finite-age iff now uses the ACTUAL selected SourcePhase
and its true local marking legality, rather than a separately supplied
occupancy groupoid character. Active/inactive coverage is complete.
Inactive labels are the prescribed zero and are inactive in the entire
actual selected Reached groupoid by the proved bridge reflection.
-/

universe u v w t
namespace CCO.ExactEPGeometry
open APCharacter APCharacter.Towers RigidGroupoid.Geometry
open RigidGroupoid.Phase CategoryTheory
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

/-- True mixed actual selected SourcePhase legality is EXACTLY the
whole corrected active orbital masks, with fixed zero inactive labels. -/
theorem originalRetainedActualSelectedMixedLegal_iff :
    let base := P.parent r
    let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
    let Q := originalExactSelectedQuotientCurrentSource A B P transport base hBase E
    let Occ := OriginalReachedOccupancy A B P base hBase E Kroot
    let anchor := originalReachedOccupancyAnchor A B P base hBase E Kroot
    let K := fun c => originalRetainedSelectedKernel A B P transport tp hOne Kroot E hE (anchor c)
    letI := originalRetainedOccupancyGroupoid A B P transport tp hOne Kroot E hE
    let χOcc := originalRetainedSelectedOccupancyCharacter A B P transport tp hOne Kroot phase E hE
    let φ := originalRetainedActualSelectedPhase A B P transport tp hOne Kroot phase E hE
    ∀ (n m : Nat) (owners : Fin n → Occ)
      (points : ∀ i, Q.Point (Quotient.mk'' (anchor (owners i)).val))
      (bits : Fin n → Bit) (inactivePoints : Fin m → Sigma Q.Point),
      (∀ j, ¬Nonempty (Bridge B.source Kroot
        (originalSelectedTaggedRepresentative A B P transport base hBase E (inactivePoints j)).1)) →
      let point : Sum (Fin n) (Fin m) → Sigma Q.Point := fun v =>
        match v with
        | Sum.inl i => ⟨Quotient.mk'' (anchor (owners i)).val,points i⟩
        | Sum.inr j => inactivePoints j
      let allBits : Sum (Fin n) (Fin m) → Bit := fun v =>
        match v with | Sum.inl i => bits i | Sum.inr _ => 0
      Age.Legal Q.source φ.masks point allBits ↔
      ∀ i j, originalSelectedCompleteAtomicMask Q (K (owners i)) (K (owners j))
        (fun (R : owners i ⟶ owners j) => χOcc.value R)
        (Q.source.colour (points i) (points j)) (bits i) (bits j) := by
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let Q := originalExactSelectedQuotientCurrentSource A B P transport base hBase E
  let CQ := exactCalculus_of_homogeneous_CCO Q.source Q.homogeneous Q.cco
  let KQ := originalRetainedSelectedKernel A B P transport tp hOne Kroot E hE (Reached.root Kroot)
  let Occ := OriginalReachedOccupancy A B P base hBase E Kroot
  let anchor := originalReachedOccupancyAnchor A B P base hBase E Kroot
  let K := fun c => originalRetainedSelectedKernel A B P transport tp hOne Kroot E hE (anchor c)
  letI := originalRetainedOccupancyGroupoid A B P transport tp hOne Kroot E hE
  let χOcc := originalRetainedSelectedOccupancyCharacter A B P transport tp hOne Kroot phase E hE
  let φ := originalRetainedActualSelectedPhase A B P transport tp hOne Kroot phase E hE
  let f := originalRetainedOccupancyToSelectedReached A B P transport tp hOne Kroot E hE
  dsimp only
  intro n m owners points bits inactivePoints hInactive
  let point : Sum (Fin n) (Fin m) → Sigma Q.Point := fun v =>
    match v with
    | Sum.inl i => ⟨Quotient.mk'' (anchor (owners i)).val,points i⟩
    | Sum.inr j => inactivePoints j
  let allBits : Sum (Fin n) (Fin m) → Bit := fun v =>
    match v with | Sum.inl i => bits i | Sum.inr _ => 0
  have hInactiveQ (j : Fin m) :
      ¬Nonempty (Bridge Q.source KQ (inactivePoints j).1) := by
    let i := originalOccupancyRepresentative A B P base hBase E (inactivePoints j).1
    have hi : (Quotient.mk'' i : OriginalOccupancy A B P base hBase E) = (inactivePoints j).1 :=
      originalOccupancyRepresentative_class A B P base hBase E (inactivePoints j).1
    intro hNew
    have hNew' : Nonempty (Bridge Q.source KQ (Quotient.mk'' i : OriginalOccupancy A B P base hBase E)) :=
      Eq.mpr (congrArg (fun c => Nonempty (Bridge Q.source KQ c)) hi) hNew
    exact hInactive j
      ((originalRetainedSelectedReached_iff A B P transport tp hOne Kroot E hE i).mp hNew')
  have hValid (v : Sum (Fin n) (Fin m)) : φ.validBit (point v).1 (allBits v) := by
    cases v with
    | inl i => exact fun hn => False.elim (hn (f (owners i)).property)
    | inr j => exact fun _ => rfl
  constructor
  · intro h i j
    exact (originalRetainedActualSelectedPhase_masks_iff A B P transport tp hOne Kroot phase E hE
      (owners i) (owners j) (Q.source.colour (points i) (points j)) (bits i) (bits j)).mp
      (h.2 (Sum.inl i) (Sum.inl j))
  · intro h
    refine ⟨hValid,?_⟩
    intro v w
    cases v with
    | inl i =>
      cases w with
      | inl j =>
        exact (originalRetainedActualSelectedPhase_masks_iff A B P transport tp hOne Kroot phase E hE
          (owners i) (owners j) (Q.source.colour (points i) (points j)) (bits i) (bits j)).mpr (h i j)
      | inr j =>
        exact φ.inactive_masks_full _ _ (hValid (Sum.inl i)) (hValid (Sum.inr j))
          (Or.inr (hInactiveQ j)) _
    | inr i =>
      exact φ.inactive_masks_full _ _ (hValid (Sum.inr i)) (hValid w)
        (Or.inl (hInactiveQ i)) _

/-- BOTH finite-age directions now consume the TRUE actual selected
SourcePhase masks, on arbitrary mixed finite selected quotient tuples.
The next chart carries child names and the COMPLETE NEW atomic palette. -/
theorem originalRetainedActualSelectedMixedLegal_iff_actualNextChart :
    let base := P.parent r
    let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
    let Q := originalExactSelectedQuotientCurrentSource A B P transport base hBase E
    let Occ := OriginalReachedOccupancy A B P base hBase E Kroot
    let anchor := originalReachedOccupancyAnchor A B P base hBase E Kroot
    let φ := originalRetainedActualSelectedPhase A B P transport tp hOne Kroot phase E hE
    ∀ (n m : Nat) (owners : Fin n → Occ)
      (points : ∀ i, Q.Point (Quotient.mk'' (anchor (owners i)).val))
      (bits : Fin n → Bit) (inactivePoints : Fin m → Sigma Q.Point),
      let point : Sum (Fin n) (Fin m) → Sigma Q.Point := fun v =>
        match v with
        | Sum.inl i => ⟨Quotient.mk'' (anchor (owners i)).val,points i⟩
        | Sum.inr j => inactivePoints j
      Function.Injective point →
      (∀ j, ¬Nonempty (Bridge B.source Kroot
        (originalSelectedTaggedRepresentative A B P transport base hBase E (inactivePoints j)).1)) →
      let old : Sum (Fin n) (Fin m) → Sigma B.Point := fun v =>
        match v with
        | Sum.inl i => ⟨(anchor (owners i)).val,
            originalSelectedReachedEclassRepresentative A B P transport hOne Kroot E
              (anchor (owners i)) (points i)⟩
        | Sum.inr j => originalSelectedTaggedRepresentative A B P transport base hBase E (inactivePoints j)
      let allBits : Sum (Fin n) (Fin m) → Bit := fun v =>
        match v with | Sum.inl i => bits i | Sum.inr _ => 0
      Age.Legal Q.source φ.masks point allBits ↔
        Nonempty (OriginalActualNextQuotientChart A B P base hBase E Kroot phase old allBits) := by
  dsimp only
  intro n m owners points bits inactivePoints hInj hInactive
  exact (originalRetainedActualSelectedMixedLegal_iff A B P transport tp hOne Kroot phase E hE
    n m owners points bits inactivePoints hInactive).trans
    (originalRetainedMixedSelectedMasks_iff_actualNextChart A B P transport tp hOne Kroot phase E hE
      n m owners points bits inactivePoints hInj hInactive)

end
end CCO.ExactEPGeometry
