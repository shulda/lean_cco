import CCO.ExactEPGeometry.OriginalRetainedAnchorGauge

/-!
# B062 C84: choose genuine reached anchors in each ORIGINAL E-component

The finite named current source has ACTUAL reached objects from the
complete old full-exact groupoid. Their original E-occupancy relation
is a true equivalence by the already proved C49 support calculus.
Quotienting the actual Reached object type gives the real components;
every class has an ACTUAL reached member, chosen with Quotient
surjectivity rather than inventing a current source object or a phase.

The anchor of two E-supported reached objects is literally the same
member. Each object is genuinely E-supported with its anchor.
This is the precise provenance for the global C84 phase normalization.
No quotient SAP, automorphism section, selected artificial generator
or change of source assumptions.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- The ORIGINAL E-support relation restricted to the entire
genuine Reached object set of an actual current full groupoid. -/
def originalReachedOccupancySetoid
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    {r : B.Sorts} (Kroot : Kernel B.source r) :
    Setoid (Reached B.source Kroot) := by
  let J := originalExactOccupancySetoid A B P base hOne E
  exact {
    r := fun b c => J.r b.val c.val
    iseqv := ⟨
      (fun b => J.refl b.val),
      (fun _ _ h => J.symm h),
      (fun _ _ _ h h' => J.trans h h')⟩
  }

/-- Every original E-occupancy component of actual Reached objects
is a literal quotient class; no external set of source objects. -/
abbrev OriginalReachedOccupancy
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    {r : B.Sorts} (Kroot : Kernel B.source r) : Type _ :=
  Quotient (originalReachedOccupancySetoid
    A B P base hOne E Kroot)

/-- Every actual E-occupancy component contains an ACTUAL Reached
object, so one such object can serve as its original-phase anchor. -/
noncomputable def originalReachedOccupancyAnchor
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (c : OriginalReachedOccupancy A B P base hOne E Kroot) :
    Reached B.source Kroot :=
  Classical.choose (Quotient.mk''_surjective c)

theorem originalReachedOccupancyAnchor_class
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (c : OriginalReachedOccupancy A B P base hOne E Kroot) :
    (Quotient.mk'' (originalReachedOccupancyAnchor
      A B P base hOne E Kroot c) :
      OriginalReachedOccupancy A B P base hOne E Kroot) = c :=
  Classical.choose_spec (Quotient.mk''_surjective c)

/-- Each actual Reached parent has one canonical anchor chosen from
its own literal original E-occupancy class. -/
noncomputable def originalReachedOccupancyAnchorOf
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (b : Reached B.source Kroot) : Reached B.source Kroot :=
  originalReachedOccupancyAnchor A B P base hOne E Kroot
    (Quotient.mk'' b)

/-- Source C84 provenance: EACH reached parent really has
nonempty original E-class occupancy with its chosen actual anchor. -/
theorem originalReachedOccupancyAnchorOf_supported
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (b : Reached B.source Kroot) :
    (originalExactOccupancySetoid A B P base hOne E).r
      b.val (originalReachedOccupancyAnchorOf
        A B P base hOne E Kroot b).val := by
  change (originalReachedOccupancySetoid
      A B P base hOne E Kroot).r
        b (originalReachedOccupancyAnchorOf
          A B P base hOne E Kroot b)
  apply Quotient.exact
  exact (originalReachedOccupancyAnchor_class A B P
    base hOne E Kroot (Quotient.mk'' b)).symm

/-- Supported current objects have LITERALLY the same selected
Reached anchor (not just equivalent anchor points). -/
theorem originalReachedOccupancyAnchorOf_eq
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (b c : Reached B.source Kroot)
    (hbc : (originalExactOccupancySetoid A B P base hOne E).r
      b.val c.val) :
    originalReachedOccupancyAnchorOf
      A B P base hOne E Kroot b =
    originalReachedOccupancyAnchorOf
      A B P base hOne E Kroot c := by
  have hClasses :
      (Quotient.mk'' b : OriginalReachedOccupancy
        A B P base hOne E Kroot) =
      Quotient.mk'' c := Quotient.sound hbc
  exact congrArg (originalReachedOccupancyAnchor
    A B P base hOne E Kroot) hClasses

end
end CCO.ExactEPGeometry
