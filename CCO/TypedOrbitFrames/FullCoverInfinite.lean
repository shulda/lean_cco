import CCO.ParityHasse.Original.RelativeIndices
import Mathlib.Order.Atoms.Finite

/-!
# B053 C31: literal infinite FULL-cover index implies every strict index is infinite

The source11 standing terminal assumption is that EVERY strict
cover in the FULL finite original invariant-equivalence lattice,
including Top covers, has infinitely many lower classes.
We keep that hypothesis verbatim and do not replace it with
the weaker no-index-two assumption or a chosen named sublattice.

For L<H choose a genuine cover L ⋖ U ≤ H in the FULL poset.
The ACTUAL L-classes of one U-class inject into the L-classes
of the ambient H-class. Hence the latter are infinite.
-/

namespace CCO.TypedOrbitFrames

open CCO.ParityHasse.Original

universe u v w
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X) {i : ι}

/-- The source11 standing infinite-index assumption, with
its exact quantifiers over all FULL original strict covers. -/
def OriginalAllFullCoversInfinite : Prop :=
  ∀ (E F : ColourEq S i), E ⋖ F →
    ∀ (x : X i), Infinite (RelativeClass E.val F.val x)

/-- C31: a strict pair L<H of ACTUAL FULL invariant
equivalences has infinite relative index in every H-class.
No distributivity, hidden SAP, CCO or finite-index
monotonicity shortcut is assumed. -/
theorem original_all_strict_full_indices_infinite
    (hCover : OriginalAllFullCoversInfinite S (i := i))
    (L H : ColourEq S i) (hLH : L < H)
    (x : X i) : Infinite (RelativeClass L.val H.val x) := by
  obtain ⟨U, hLU, hUH⟩ := hLH.exists_covby_le
  haveI : Infinite (RelativeClass L.val U.val x) :=
    hCover L U hLU x
  exact Infinite.of_injective
    (relativeInclusion L.val U.val H.val hUH x)
    (relativeInclusion_injective L.val U.val H.val hUH x)

end CCO.TypedOrbitFrames
