import CCO.ExactEPGeometry.SelectedSortSource

/-!
# B062 C105: terminality under an actual injective sort selection

A selected-sort source keeps the COMPLETE current orbital palette
and actual carriers on an injectively chosen set of named sorts.
Its full colour-invariant equivalences on an individual selected
sort are literally the original colour-invariant equivalences on
that carrier, and the relative-class type is unchanged.

Consequently CurrentSource.Terminal descends to ANY such selected
subsource. This uses NO exactness, SAP, quotient source theorem,
or extra terminality provider: it is just literal restriction to
the same original sorts, without identifying independent carriers.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter.Towers
open CCO.ParityHasse.Original

noncomputable section

/-- Genuine all-sort terminality is inherited by the actual
injectively selected subsource, for the FULL invariant-equivalence
lattice and its finite-relative-index obstruction. -/
theorem selectedSortCurrentSource_terminal
    (B : CurrentSource.{u,v,w,t}) {K : Type u} [Fintype K]
    (f : K ↪ B.Sorts)
    (hTerminal : B.Terminal) :
    (selectedSortCurrentSource B f).Terminal := by
  change ¬(selectedSortCurrentSource B f).Obstruction
  rintro ⟨k,E,F,a,hEF,hFin⟩
  let EE : ColourEq B.source (f k) := ⟨E.val,E.property⟩
  let FF : ColourEq B.source (f k) := ⟨F.val,F.property⟩
  have hLt : EE < FF := hEF
  have hFinite : Finite (RelativeClass EE.val FF.val a) := hFin
  exact hTerminal ⟨f k,EE,FF,a,hLt,hFinite⟩

end
end CCO.ExactEPGeometry
