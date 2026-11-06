import CCO.ParityHasse.Original.Equivalences

/-!
# B053 D04/C27,C29: genuine original class-incidence fibre geometry

For actual FULL original colour-invariant equivalences E_i, a
nonempty intersection of their actual classes is one class of the
literal family-meet relation H. This is the algebraic conclusion
of source11 C27 AFTER original exact-ball Helly supplies a
common real witness. No witness, Helly property, distributivity
or hidden SAP is created by this lemma.

If one E_i is below a proper original invariant J, all points
of the common fibre have the SAME genuine J-coordinate.
Namedness is a further restriction on represented endpoints.
-/

namespace CCO.TypedOrbitFrames

open CCO.ParityHasse.Original

universe u v w
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {i : ι} {m : Nat}

/-- Literal intersection of finitely many ACTUAL old equivalence
classes, including the empty family's entire original real sort. -/
def originalActualClassFibre
    (E : Fin m → ColourEq S i) (c : Fin m → X i) : Set (X i) :=
  {y | ∀ j, E j (c j) y}

/-- The actual finite family meet H, read pointwise, not a new
named non-MI quotient coordinate. -/
def originalActualFamilyMeetClass
    (E : Fin m → ColourEq S i) (x : X i) : Set (X i) :=
  {y | ∀ j, E j x y}

/-- With one COMMON old real witness, the intersection of actual
E_i classes is precisely the H-class of that real witness. -/
theorem original_actual_family_fibre_eq_meet_class
    (E : Fin m → ColourEq S i) (c : Fin m → X i) (x : X i)
    (hx : ∀ j, E j (c j) x) :
    originalActualClassFibre S E c =
      originalActualFamilyMeetClass S E x := by
  ext y
  constructor
  · intro hy j
    exact (E j).val.trans ((E j).val.symm (hx j)) (hy j)
  · intro hy j
    exact (E j).val.trans (hx j) (hy j)

/-- For the EMPTY family the actual incidence fibre is all reals,
not an artificial singleton or a nullary named coordinate. -/
theorem original_actual_empty_class_fibre
    (E : Fin 0 → ColourEq S i) (c : Fin 0 → X i) :
    originalActualClassFibre S E c = (Set.univ : Set (X i)) := by
  ext y
  simp [originalActualClassFibre]

/-- If ONE actual E_i lies below J, every two points in the
common real class-incidence fibre have identical genuine
J-equivalence class. No quotient-language naming is assumed. -/
theorem original_actual_fibre_forced_coordinate
    (E : Fin m → ColourEq S i) (c : Fin m → X i)
    (J : ColourEq S i) (j : Fin m) (hEJ : E j ≤ J)
    {x y : X i}
    (hx : x ∈ originalActualClassFibre S E c)
    (hy : y ∈ originalActualClassFibre S E c) :
    J x y := by
  have h : E j x y :=
    (E j).val.trans ((E j).val.symm (hx j)) (hy j)
  exact hEJ h

end CCO.TypedOrbitFrames
