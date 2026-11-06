import CCO.ExactEPGeometry.OriginalSelectedGlobalClassReadout
import CCO.ExactEPGeometry.OriginalReachedOccupancyAnchors

/-!
# B062 C95: mixed selected quotient vertices have distinct GLOBAL E-classes

The finite reached representatives and canonical inactive representatives
used in the real marked-age chart preserve the exact selected E-class,
even when their old named parents differ. Hence distinct selected quotient
vertices stay distinct after quotienting the WHOLE tagged old carrier by
the original E. Point injectivity alone would not imply this statement.

No inactivity premise is needed for this particular no-collapse fact;
actual inactivity remains a separate premise of marked-age realization.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- The mixed representatives of distinct actual selected quotient
vertices have distinct original GLOBAL E-classes, not merely distinct
points or projected gate classes. -/
theorem originalRetainedMixedSelectedOld_globalE_injective
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (hOne : ∀ i j : A.Sorts, i = j)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (E : ExactEq A.source (P.parent r)) :
    let base := P.parent r
    let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
    let Occ := OriginalReachedOccupancy A B P base hBase E Kroot
    let Q := originalExactSelectedQuotientCurrentSource
      A B P transport base hBase E
    let anchor := originalReachedOccupancyAnchor
      A B P base hBase E Kroot
    ∀ (n m : Nat)
      (owners : Fin n → Occ)
      (points : ∀ i : Fin n,
        Q.Point (Quotient.mk'' (anchor (owners i)).val))
      (inactivePoints : Fin m → Sigma Q.Point),
      Function.Injective (fun v : Sum (Fin n) (Fin m) =>
        match v with
        | Sum.inl i =>
            (⟨(Quotient.mk'' (anchor (owners i)).val :
              OriginalOccupancy A B P base hBase E),points i⟩ :
              Sigma Q.Point)
        | Sum.inr j => inactivePoints j) →
      Function.Injective (fun v : Sum (Fin n) (Fin m) =>
        (Quotient.mk''
          (match v with
          | Sum.inl i =>
              (⟨(anchor (owners i)).val,
                originalSelectedReachedEclassRepresentative
                  A B P transport hOne Kroot E
                    (anchor (owners i)) (points i)⟩ : Sigma B.Point)
          | Sum.inr j =>
              originalSelectedTaggedRepresentative
                A B P transport base hBase E (inactivePoints j)) :
          Quotient (currentOriginalExactSetoid A B P base hBase E))) := by
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let Occ := OriginalReachedOccupancy A B P base hBase E Kroot
  let Q := originalExactSelectedQuotientCurrentSource
    A B P transport base hBase E
  let anchor := originalReachedOccupancyAnchor
    A B P base hBase E Kroot
  dsimp only
  intro n m owners points inactivePoints hSelected
  let selected : Sum (Fin n) (Fin m) → Sigma Q.Point := fun v =>
    match v with
    | Sum.inl i =>
        ⟨(Quotient.mk'' (anchor (owners i)).val :
          OriginalOccupancy A B P base hBase E),points i⟩
    | Sum.inr j => inactivePoints j
  let old : Sum (Fin n) (Fin m) → Sigma B.Point := fun v =>
    match v with
    | Sum.inl i =>
        ⟨(anchor (owners i)).val,
          originalSelectedReachedEclassRepresentative
            A B P transport hOne Kroot E
              (anchor (owners i)) (points i)⟩
    | Sum.inr j =>
        originalSelectedTaggedRepresentative
          A B P transport base hBase E (inactivePoints j)
  have hClass : ∀ v : Sum (Fin n) (Fin m),
      (Quotient.mk'' (old v) :
        Quotient (currentOriginalExactSetoid A B P base hBase E)) =
      Quotient.mk'' (originalSelectedTaggedRepresentative
        A B P transport base hBase E (selected v)) := by
    intro v
    cases v with
    | inl i =>
      exact originalSelectedReachedRepresentative_globalE
        A B P transport hOne Kroot E (anchor (owners i)) (points i)
    | inr j => rfl
  change Function.Injective (fun v : Sum (Fin n) (Fin m) =>
    (Quotient.mk'' (old v) :
      Quotient (currentOriginalExactSetoid A B P base hBase E)))
  intro i j hij
  apply hSelected
  apply originalSelectedTaggedRepresentative_globalE_injective
    A B P transport base hBase E
  exact (hClass i).symm.trans (hij.trans (hClass j))

end
end CCO.ExactEPGeometry
