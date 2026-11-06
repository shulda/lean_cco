import CCO.ExactEPGeometry.OriginalAllCurrentFullInvariantTerminal
import CCO.ExactEPGeometry.SelectedSortTerminal
import CCO.ExactEPGeometry.OriginalOccupancyQuotientSource

/-!
# B062 C105: actual one-parent-per-original-E-occupancy quotient terminality

First construct the GENUINE all-parent simultaneous exact quotient
of the terminal current AP+HOM CCO prefix and transfer its COMPLETE
invariant-equivalence obstruction via literal surjective quotient
maps. Then use the actual injective representative-parent selection
which changes neither underlying quotient points nor pair colours.

All invariant equivalences participate, including non-RAW-exact ones.
The source terminality hypothesis belongs ONLY to this conditional
last implication. The full quotient safe tower C103–C104 is not
replaced by this theorem.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter.Towers

noncomputable section

/-- The C105 terminality implication on the ACTUAL current
occupancy-indexed selected original E-quotient, with its genuine
CurrentSource and complete invariant-equivalence lattice. -/
theorem originalExactSelectedQuotient_terminal
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    (hTerminal : B.Terminal) :
    (originalExactSelectedQuotientCurrentSource
      A B P transport base hOne E).Terminal := by
  let Occ := OriginalOccupancy A B P base hOne E
  letI : Finite Occ := originalOccupancyFinite A B P base hOne E
  letI : Fintype Occ := Fintype.ofFinite Occ
  let Qall := originalExactAllCurrentQuotientCurrentSource
    A B P transport base hOne E
  let σ : Occ ↪ B.Sorts :=
    originalOccupancyRepresentativeEmbedding A B P base hOne E
  change (selectedSortCurrentSource Qall σ).Terminal
  exact selectedSortCurrentSource_terminal Qall σ
    (originalAllCurrentQuotient_terminal
      A B P transport base hOne E hTerminal)

end
end CCO.ExactEPGeometry
