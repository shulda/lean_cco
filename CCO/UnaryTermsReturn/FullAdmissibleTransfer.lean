import CCO.UnaryTermsReturn.ActualGeneratedClosures
import Mathlib.Data.Set.Card

/-!
# B052 C13–C15: FULL induced one-generator admissibility transfer

The source10 unary-admissibility condition is NOT a bound for
arbitrary partial structures with total unary symbols. It requires
for EVERY generator a FULL induced hidden-diagram isomorphism to
one ACTUAL completed one-generated member. The full diagram
includes ALL named total unary operations, literal equality
and ALL internal named binary relations.

Here the unary symbols are represented by their total actions
on a tagged carrier; arbitrary many-sorted unary operations can
be interpreted with a source-tag guard and unchanged values
outside their own source sort. The data of each full induced
isomorphism explicitly include unary closure and binary
preservation; a cardinality-only bijection is NOT the definition
of an admissible source.

The size transfer is elementary: an actual finite uniform
one-generator upper bound transports along that full
isomorphism. Importantly this does not assert existence
of an isomorphism for an arbitrary partial hidden source.
-/

universe u v w t

namespace CCO.UnaryTermsReturn

/-- Exact FULL induced hidden-diagram isomorphism over
one unary-closed source fragment and one genuinely
completed ambient fragment. Both named unary functions
and all named binary predicates are part of the data,
not merely the number of points or the unary graph. -/
structure FullInducedUnaryBinaryIso
    {C : Type u} {A : Type v}
    (U : Type w) (B : Type t)
    (unaryC : U → C → C) (unaryA : U → A → A)
    (binaryC : B → C → C → Prop)
    (binaryA : B → A → A → Prop)
    (source : Set C) (actual : Set A) where
  toEquiv : source ≃ actual
  sourceClosed : ∀ f x, x ∈ source → unaryC f x ∈ source
  actualClosed : ∀ f x, x ∈ actual → unaryA f x ∈ actual
  preservesUnary : ∀ (f : U) (x : source),
    toEquiv
      (⟨unaryC f x.val,
        sourceClosed f x.val x.property⟩ : source) =
    (⟨unaryA f (toEquiv x).val,
      actualClosed f (toEquiv x).val
        (toEquiv x).property⟩ : actual)
  preservesBinary : ∀ (b : B) (x y : source),
    binaryC b x.val y.val ↔
      binaryA b (toEquiv x).val (toEquiv y).val

namespace FullInducedUnaryBinaryIso

variable {C : Type u} {A : Type v}
variable {U : Type w} {B : Type t}
variable {unaryC : U → C → C} {unaryA : U → A → A}
variable {binaryC : B → C → C → Prop}
variable {binaryA : B → A → A → Prop}
variable {source : Set C} {actual : Set A}

theorem preservesLiteralEquality
    (e : FullInducedUnaryBinaryIso U B unaryC unaryA
      binaryC binaryA source actual)
    (x y : source) :
    (e.toEquiv x = e.toEquiv y) ↔ x = y := by
  constructor
  · exact e.toEquiv.injective
  · intro h
    exact congrArg e.toEquiv h

/-- There is no cardinality hypothesis in the ISOMORPHISM:
the true full induced diagram equivalence gives exact
cardinality, including the finite case relevant to HN. -/
theorem exactNcard
    (e : FullInducedUnaryBinaryIso U B unaryC unaryA
      binaryC binaryA source actual) :
    source.ncard = actual.ncard :=
  Set.ncard_congr' e.toEquiv

end FullInducedUnaryBinaryIso

/-- Source10's unary-admissibility, stated at its correct
quantifier strength: for EVERY source vertex, its full induced
one-generated closure has an ACTUAL completed witness. The
isomorphism carries unary operations, equality and binary data.
Nothing assumes the WHOLE partial source is completed or
admits a homomorphism-embedding completion. -/
def FullUnaryAdmissible
    {C : Type u} {A : Type v}
    (U : Type w) (B : Type t)
    (unaryC : U → C → C) (unaryA : U → A → A)
    (binaryC : B → C → C → Prop)
    (binaryA : B → A → A → Prop)
    (closureC : C → Set C) (closureA : A → Set A) : Prop :=
  ∀ x : C, ∃ y : A,
    Nonempty (FullInducedUnaryBinaryIso U B
      unaryC unaryA binaryC binaryA (closureC x) (closureA y))

/-- B052 C14: the FULL admissibility hypothesis transfers any
ACTUAL uniform one-generator bound to each partial generator.
No hidden amalgamation or HN theorem is invoked. -/
theorem full_unary_admissible_transfer_uniform
    {C : Type u} {A : Type v}
    (U : Type w) (B : Type t)
    (unaryC : U → C → C) (unaryA : U → A → A)
    (binaryC : B → C → C → Prop)
    (binaryA : B → A → A → Prop)
    (closureC : C → Set C) (closureA : A → Set A)
    (m : Nat)
    (hActual : ∀ y : A, (closureA y).ncard ≤ m)
    (hAdmissible : FullUnaryAdmissible U B unaryC unaryA
      binaryC binaryA closureC closureA)
    (x : C) :
    (closureC x).ncard ≤ m := by
  obtain ⟨y, ⟨e⟩⟩ := hAdmissible x
  rw [e.exactNcard]
  exact hActual y

end CCO.UnaryTermsReturn
