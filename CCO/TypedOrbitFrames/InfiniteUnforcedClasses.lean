import CCO.TypedOrbitFrames.FullCoverInfinite
import CCO.TypedOrbitFrames.OriginalClassFibre

/-!
# B053 C30–C34: actual infinite J-coordinate classes in an old H-fibre

Under the source11 literal standing assumption that EVERY strict
cover in the FULL original invariant-equivalence lattice has infinite
relative index (including the top covers), an H-class meets
INFINITELY MANY J-classes whenever H is not contained in J.

The proof uses actual old Setoid quotient classes and an injective
map from the genuine relative (H ⊓ J)-class quotient inside H
to the set of genuine J-classes present in that real H-fibre.
This is stronger than merely making the global quotient infinite.

No distributivity, imaginary quotient-age SAP, hidden group
homogeneity, original semantic CCO or finite-class cardinality
convention is used. It is a source-specific building block for
the joint exact Helly-fibre dichotomy, which separately needs
the common original real witness and meet-prime finite lattice.
-/

namespace CCO.TypedOrbitFrames

open CCO.ParityHasse.Original

universe u v w
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X) {i : ι}

/-- Actual original J-quotient points occurring among REAL points
of the fixed original H-class of x; no hidden namedness assumption. -/
def originalJClassesWithinHClass
    (H J : ColourEq S i) (x : X i) : Set (Quotient J.val) :=
  {q | ∃ y : X i, H x y ∧ Quotient.mk J.val y = q}

/-- Each class of the TRUE relative equivalence H ⊓ J in the
actual H-class yields one existing J-class in that same H-class. -/
def originalRelativeClassToActualJ
    (H J : ColourEq S i) (x : X i) :
    RelativeClass (H ⊓ J).val H.val x →
      {q : Quotient J.val // q ∈ originalJClassesWithinHClass S H J x} :=
  Quotient.lift
    (fun y : {y : X i // H.val x y} =>
      ⟨Quotient.mk J.val y.val, ⟨y.val, y.property, rfl⟩⟩)
    (by
      intro y z h
      apply Subtype.ext
      exact Quotient.sound h.2)

/-- The preceding map is INJECTIVE on old relative quotient
classes, even if the whole old H-class has infinite real points.
Equality of J-classes plus membership in the common H-class
forces precisely the same H⊓J-equivalence class. -/
theorem original_relative_to_J_injective
    (H J : ColourEq S i) (x : X i) :
    Function.Injective (originalRelativeClassToActualJ S H J x) := by
  intro q r h
  induction q using Quotient.inductionOn with
  | _ y =>
    induction r using Quotient.inductionOn with
    | _ z =>
      have hJ : Quotient.mk J.val y.val = Quotient.mk J.val z.val :=
        congrArg Subtype.val h
      apply Quotient.sound
      have hH : H.val y.val z.val :=
        H.val.trans (H.val.symm y.property) z.property
      exact ⟨hH, Quotient.exact hJ⟩

/-- Source11 C31/C33: for every REAL old H-class and every
original full invariant J with H not below J, that class meets
infinitely many DISTINCT ACTUAL J-quotient points. The
quantification includes Top-cover cases and does not interpret
a zero Nat.card as a finite value. -/
theorem original_unforced_J_classes_in_H_fibre_infinite
    (hCover : OriginalAllFullCoversInfinite S (i := i))
    (H J : ColourEq S i) (hnot : ¬ H ≤ J) (x : X i) :
    Infinite {q : Quotient J.val //
        q ∈ originalJClassesWithinHClass S H J x} := by
  have hle : H ⊓ J ≤ H := inf_le_left
  have hne : H ⊓ J ≠ H := by
    intro h
    apply hnot
    calc
      H = H ⊓ J := h.symm
      _ ≤ J := inf_le_right
  have hlt : H ⊓ J < H := lt_of_le_of_ne hle hne
  haveI : Infinite (RelativeClass (H ⊓ J).val H.val x) :=
    original_all_strict_full_indices_infinite S hCover
      (H ⊓ J) H hlt x
  exact Infinite.of_injective
    (originalRelativeClassToActualJ S H J x)
    (original_relative_to_J_injective S H J x)

end CCO.TypedOrbitFrames
