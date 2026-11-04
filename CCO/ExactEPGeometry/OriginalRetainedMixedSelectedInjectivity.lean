import CCO.ExactEPGeometry.OriginalSelectedFiniteReachedInjectivity
import CCO.ExactEPGeometry.OriginalSelectedFiniteRepresentatives

/-!
# B062 C96: mixed genuine E-quotient vertices have distinct old representatives

On every ACTUAL selected original-E quotient prefix, a family of
distinct reached quotient vertices has distinct original points by
C90's exact selected-class right inverse. Independently, C66's
canonical tagged old representative is injective on all genuine
selected quotient vertices. A reached old parent and a genuinely
inactive selected old parent are DISJOINT sorts, so the two finite
old representative families have disjoint images.

This removes the extra unproved injective old-representative
premise in the earlier mixed C96 old marked chart, provided the
vertices are genuine selected E-quotient vertices (not an invented
abstract quotient age). No SAP, group section or extra exactness.
-/

universe u v w t z

namespace CCO.ExactEPGeometry

open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- Combine two injective real-point families with disjoint images. -/
private theorem injective_sum_of_disjoint
    {X : Type u} {Y : Type v} {Z : Type w}
    (f : X → Z) (g : Y → Z)
    (hf : Function.Injective f)
    (hg : Function.Injective g)
    (hfg : ∀ x y, f x ≠ g y) :
    Function.Injective (fun x : Sum X Y =>
      match x with
      | Sum.inl a => f a
      | Sum.inr b => g b) := by
  intro x y h
  cases x with
  | inl a =>
    cases y with
    | inl b => exact congrArg Sum.inl (hf h)
    | inr b => exact False.elim (hfg a b h)
  | inr a =>
    cases y with
    | inl b => exact False.elim (hfg b a h.symm)
    | inr b => exact congrArg Sum.inr (hg h)

/-- Every finite family of pairwise distinct REAL selected original-E
quotient points, split into reached anchor objects and actually
inactive selected sorts, admits a jointly injective fine-old
representative diagram. The reached representative is the EXACT
chosen E-quotient vertex (not merely its projected K/E gate class);
the inactive representative is the actual C66 chosen E-class
member. Inactive status is tested on its TRUE canonical old sort. -/
theorem originalRetainedMixedSelectedOld_injective
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
      (∀ j : Fin m,
        ¬Nonempty (Bridge B.source Kroot
          (originalSelectedTaggedRepresentative
            A B P transport base hBase E (inactivePoints j)).1)) →
      Function.Injective (fun v : Sum (Fin n) (Fin m) =>
        match v with
        | Sum.inl i =>
            (⟨(anchor (owners i)).val,
              originalSelectedReachedEclassRepresentative
                A B P transport hOne Kroot E
                  (anchor (owners i)) (points i)⟩ : Sigma B.Point)
        | Sum.inr j =>
            originalSelectedTaggedRepresentative
              A B P transport base hBase E (inactivePoints j)) := by
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let Occ := OriginalReachedOccupancy A B P base hBase E Kroot
  let Q := originalExactSelectedQuotientCurrentSource
    A B P transport base hBase E
  let anchor := originalReachedOccupancyAnchor
    A B P base hBase E Kroot
  dsimp only
  intro n m owners points inactivePoints hSelected hInactive
  let active : Fin n → Sigma B.Point := fun i =>
    ⟨(anchor (owners i)).val,
      originalSelectedReachedEclassRepresentative
        A B P transport hOne Kroot E
          (anchor (owners i)) (points i)⟩
  let inactive : Fin m → Sigma B.Point := fun j =>
    originalSelectedTaggedRepresentative
      A B P transport base hBase E (inactivePoints j)
  have hActiveSelected : Function.Injective
      (fun i : Fin n =>
        (⟨(Quotient.mk'' (anchor (owners i)).val :
          OriginalOccupancy A B P base hBase E),points i⟩ :
          Sigma Q.Point)) := by
    intro i j hij
    have hEq : (Sum.inl i : Sum (Fin n) (Fin m)) =
        Sum.inl j := hSelected hij
    cases hEq
    rfl
  have hInactiveSelected : Function.Injective inactivePoints := by
    intro i j hij
    have hEq : (Sum.inr i : Sum (Fin n) (Fin m)) =
        Sum.inr j := hSelected hij
    cases hEq
    rfl
  have hActiveOld : Function.Injective active :=
    originalSelectedFiniteReachedRepresentative_injective
      A B P transport hOne Kroot E owners points hActiveSelected
  have hInactiveOld : Function.Injective inactive :=
    (originalSelectedTaggedRepresentative_injective
      A B P transport base hBase E).comp hInactiveSelected
  have hDisjoint : ∀ i j, active i ≠ inactive j := by
    intro i j hEq
    have hOwners : (anchor (owners i)).val = (inactive j).1 :=
      congrArg Sigma.fst hEq
    have hReached : Nonempty (Bridge B.source Kroot
        (anchor (owners i)).val) := (anchor (owners i)).property
    have hNotReached : ¬Nonempty (Bridge B.source Kroot
        (inactive j).1) := hInactive j
    exact hNotReached (hOwners ▸ hReached)
  change Function.Injective (fun v : Sum (Fin n) (Fin m) =>
    match v with
    | Sum.inl i => active i
    | Sum.inr j => inactive j)
  exact injective_sum_of_disjoint active inactive
    hActiveOld hInactiveOld hDisjoint

end
end CCO.ExactEPGeometry
