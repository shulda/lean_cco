import CCO.TypedOrbitFrames.InfiniteUnforcedClasses
import CCO.TypedOrbitFrames.OriginalClassFibre

/-!
# B053 D04 / C27,C29,C31--C34: literal full original finite family meet

The source11 class-incidence fibre is an intersection of genuine old
classes for finitely many FULL original colour-invariant equivalences
E_j on ONE original real sort, not an invented hidden quotient.
For the empty family the resulting old equivalence is Top.

Given ONE actual old common real point, the intersection of
specified E_j classes is exactly its H-class. The already
compiled full-cover infinite-index theorem gives infinitely
many ACTUAL J-quotient points in this same common old fibre
when H is not below J.

Original exact-ball Helly must SEPARATELY supply the common point;
neither a finite family of actual classes nor its pairwise
compatibility alone is a witness here. Meet-prime forced coordinates
and one-action simultaneous finite avoidance are distinct obligations.
-/

namespace CCO.TypedOrbitFrames

open CCO.ParityHasse.Original

universe u v w
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X) {i : ι} {m : Nat}

/-- Genuine FULL original invariant-equivalence intersection.
No non-MI hidden quotient coordinate is added to the signature. -/
def originalActualMeetEquivalence
    (E : Fin m → ColourEq S i) : ColourEq S i where
  val := {
    r := fun x y => ∀ j, E j x y
    iseqv := ⟨
      (by intro x j; exact (E j).val.refl x),
      (by intro x y h j; exact (E j).val.symm (h j)),
      (by intro x y z hxy hyz j;
          exact (E j).val.trans (hxy j) (hyz j))⟩
  }
  property := by
    intro x y x' y' hc
    constructor
    · intro h j
      exact ((E j).property x y x' y' hc).mp (h j)
    · intro h j
      exact ((E j).property x y x' y' hc).mpr (h j)

@[simp] theorem original_actual_meet_equivalence_apply
    (E : Fin m → ColourEq S i) (x y : X i) :
    originalActualMeetEquivalence S E x y ↔ ∀ j, E j x y := Iff.rfl

/-- Universal finite meet in the FULL original invariant family. -/
theorem original_actual_meet_equivalence_is_glb
    (E : Fin m → ColourEq S i) (K : ColourEq S i) :
    K ≤ originalActualMeetEquivalence S E ↔ ∀ j, K ≤ E j := by
  constructor
  · intro h j x y hxy
    exact (h x y hxy) j
  · intro h x y hxy j
    exact h j x y hxy

/-- Once an actual real witness is supplied, the class
intersection is exactly ONE genuine original full-meet class. -/
theorem original_actual_class_fibre_eq_full_meet_class
    (E : Fin m → ColourEq S i) (c : Fin m → X i)
    (x : X i) (hx : x ∈ originalActualClassFibre S E c) :
    originalActualClassFibre S E c =
      {y : X i | originalActualMeetEquivalence S E x y} := by
  rw [original_actual_family_fibre_eq_meet_class S E c x hx]
  rfl

/-- Empty family equals the genuine old Top, not a
represented nonidentity meet-irreducible name. -/
theorem original_actual_empty_meet_is_top
    (E : Fin 0 → ColourEq S i) :
    originalActualMeetEquivalence S E = ⊤ := by
  apply ColourEq.ext S i
  intro x y
  constructor
  · intro _
    trivial
  · intro _ j
    exact Fin.elim0 j

/-- Source11 C31/C33 specialized to an ACTUAL compatible old
class incidence fibre. The FULL strict-cover hypothesis
includes Top covers. The common real x is explicitly assumed;
it will later be supplied by genuine old exact-ball Helly. -/
theorem original_unforced_J_classes_in_actual_common_fibre
    (hCover : OriginalAllFullCoversInfinite S (i := i))
    (E : Fin m → ColourEq S i) (c : Fin m → X i)
    (x : X i) (hx : x ∈ originalActualClassFibre S E c)
    (J : ColourEq S i)
    (hnot : ¬ originalActualMeetEquivalence S E ≤ J) :
    Infinite {q : Quotient J.val //
       ∃ y : X i, y ∈ originalActualClassFibre S E c ∧
         Quotient.mk J.val y = q} := by
  let H : ColourEq S i := originalActualMeetEquivalence S E
  have hinf :
      Infinite {q : Quotient J.val //
        q ∈ originalJClassesWithinHClass S H J x} :=
    original_unforced_J_classes_in_H_fibre_infinite
      S hCover H J hnot x
  have hclass :
      originalActualClassFibre S E c =
        {y : X i | H x y} :=
    original_actual_class_fibre_eq_full_meet_class S E c x hx
  have hsets :
      originalJClassesWithinHClass S H J x =
      {q : Quotient J.val |
        ∃ y : X i, y ∈ originalActualClassFibre S E c ∧
          Quotient.mk J.val y = q} := by
    ext q
    constructor
    · rintro ⟨y, hy, hq⟩
      refine ⟨y, ?_, hq⟩
      rw [hclass]
      exact hy
    · rintro ⟨y, hy, hq⟩
      refine ⟨y, ?_, hq⟩
      rw [hclass] at hy
      exact hy
  rw [hsets] at hinf
  exact hinf

end CCO.TypedOrbitFrames
