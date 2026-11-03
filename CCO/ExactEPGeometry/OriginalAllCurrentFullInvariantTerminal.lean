import CCO.ExactEPGeometry.OriginalAllCurrentFullInvariantQuotient
import CCO.ExactEPGeometry.RelativeIndexQuotientTransport

/-!
# B062 C105: terminality of the TRUE all-parent original E quotient

The quotient of a genuine current AP+HOM CCO prefix by every actual
original full RAW exact kernel E|p² is a previously constructed real
homogeneous simultaneous quotient. Its full invariant-equivalence
lattice, NOT just its exact sublattice, is lifted along each literal
surjective quotient projection.

A proper FINITE relative-index interval below lifts to a proper
FINITE interval above. The original CurrentSource.Terminal hypothesis
forbids exactly such intervals (its Obstruction is a strict interval,
not merely a conveniently selected cover). This proves the all-parent
quotient terminal without a quotient SAP, a quotient automorphism
section, or any exactness assumption on the two tested equivalences.

It does NOT assert the final one-parent-per-occupancy selected quotient
or the full safe tower construction. Those need independent retyping
and genuine complete marked-age induction.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter.Towers
open RigidGroupoid.Geometry
open CCO.ParityHasse.Original

noncomputable section

/-- A proper interval of arbitrary, actually colour-invariant
equivalences on the real all-parent quotient remains strict when
pulled back to the old current parent. No exactness hypothesis on
either equivalence, and no quotient group section. -/
theorem originalAllCurrentFullInvariantPullback_strict
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    {p : B.Sorts}
    (U V : ColourEq
      (originalExactAllCurrentQuotientCurrentSource
        A B P transport base hOne E).source p)
    (hUV : U < V) :
    originalAllCurrentFullInvariantPullback
      A B P transport base hOne E U <
    originalAllCurrentFullInvariantPullback
      A B P transport base hOne E V := by
  let Q := originalExactAllCurrentQuotientCurrentSource
    A B P transport base hOne E
  let π : B.Point p → Q.Point p := fun a => Quotient.mk'' a
  let EU := originalAllCurrentFullInvariantPullback
    A B P transport base hOne E U
  let EV := originalAllCurrentFullInvariantPullback
    A B P transport base hOne E V
  have hLE : EU ≤ EV := by
    intro x y h
    change U (π x) (π y) at h
    change V (π x) (π y)
    exact hUV.le h
  have hNE : EU ≠ EV := by
    intro heq
    have hVU : V ≤ U := by
      intro q r h
      obtain ⟨x,hx⟩ := Quotient.mk''_surjective q
      obtain ⟨y,hy⟩ := Quotient.mk''_surjective r
      have hv : EV x y := by
        change V (π x) (π y)
        simpa only [hx,hy] using h
      rw [← heq] at hv
      have hu : U (π x) (π y) := hv
      simpa only [hx,hy] using hu
    exact hUV.ne (le_antisymm hUV.le hVU)
  exact lt_of_le_of_ne hLE hNE

/-- The literal E-quotient of an already terminal ACTUAL current
source is terminal, as an all-parent homogeneous quotient source.
This is A03's full-invariant terminality implication, independent
of any source maximal-character step or quotient SAP. -/
theorem originalAllCurrentQuotient_terminal
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    (hTerm : B.Terminal) :
    (originalExactAllCurrentQuotientCurrentSource
      A B P transport base hOne E).Terminal := by
  let Q := originalExactAllCurrentQuotientCurrentSource
    A B P transport base hOne E
  change ¬ Q.Obstruction
  rintro ⟨p,U,V,q,hUV,hFinite⟩
  let π : B.Point p → Q.Point p := fun z => Quotient.mk'' z
  obtain ⟨x,hx⟩ := Quotient.mk''_surjective q
  let EU : ColourEq B.source p :=
    originalAllCurrentFullInvariantPullback
      A B P transport base hOne E U
  let EV : ColourEq B.source p :=
    originalAllCurrentFullInvariantPullback
      A B P transport base hOne E V
  have hStrict : EU < EV :=
    originalAllCurrentFullInvariantPullback_strict
      A B P transport base hOne E U V hUV
  letI : Finite (RelativeClass U.val V.val (π x)) := by
    simpa only [hx] using hFinite
  have hEu : ∀ a b : B.Point p,
      EU a b ↔ U (π a) (π b) := fun _ _ => Iff.rfl
  have hEv : ∀ a b : B.Point p,
      EV a b ↔ V (π a) (π b) := fun _ _ => Iff.rfl
  let e := relativeClassEquiv_of_surjective_pullback
    π Quotient.mk''_surjective EU.val EV.val
      U.val V.val hEu hEv x
  have hFinOld : Finite (RelativeClass EU.val EV.val x) :=
    Finite.of_injective e e.injective
  exact hTerm ⟨p,EU,EV,x,hStrict,hFinOld⟩

end
end CCO.ExactEPGeometry
