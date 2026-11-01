import CCO.ExactEPGeometry.SelectedSortExactWords
import CCO.ExactEPGeometry.OriginalOccupancyClassEquivariance
import CCO.ExactEPGeometry.OriginalOccupancyQuotientSource

/-!
# B062 C82: the actual selected quotient retyping data

For a single ORIGINAL full exact E and every current named sort i,
the canonical original E-occupancy class [i] has one ACTUAL selected
representative sort. C49 proves that every individual global E-class
occupying i also occupies that representative; C66 proves uniqueness.
Consequently the canonical local E-class map is a genuine bijection.
The C83 equivariance theorem proves that it intertwines the SAME
actual quotient B.G action, on the entire literal quotient carrier.

This constructs the precise SelectedRetyping certificate needed to
turn every whole all-parent RAW word (including equality and all its
intermediate sorts) into a selected-source RAW word. This is not a
group section, arbitrary sort deletion, SAP, or an assumed quotient
full-exactness provider.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter.Towers

noncomputable section

/-- Every named sort of the actual all-parent quotient is genuinely
equivariantly equivalent to the chosen representative of its
original E-occupancy component. This is the real C82 instantiation
of the generic finite-word retyping certificate. -/
noncomputable def originalSelectedSortRetyping
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base) :
    let Q := originalExactAllCurrentQuotientCurrentSource
      A B P transport base hOne E
    letI : ∀ i : Q.Sorts, MulAction B.G (Q.Point i) := Q.action
    SelectedRetyping (X := Q.Point)
      (originalOccupancyRepresentativeEmbedding
        A B P base hOne E) (G := B.G) := by
  let Q : CurrentSource.{u,v,v,t} :=
    originalExactAllCurrentQuotientCurrentSource
      A B P transport base hOne E
  letI : ∀ i : B.Sorts, MulAction B.G (Q.Point i) := Q.action
  let C := OriginalOccupancy A B P base hOne E
  let σ : C ↪ B.Sorts :=
    originalOccupancyRepresentativeEmbedding A B P base hOne E
  letI : Finite C := originalOccupancyFinite A B P base hOne E
  letI : Fintype C := Fintype.ofFinite C
  have hSup : ∀ i : B.Sorts,
      (originalExactOccupancySetoid A B P base hOne E).r
        i (σ (Quotient.mk'' i : C)) := by
    intro i
    apply Quotient.exact
    exact (originalOccupancyRepresentative_class
      A B P base hOne E (Quotient.mk'' i : C)).symm
  exact {
    target := fun i => (Quotient.mk'' i : C)
    pointEquiv := fun i =>
      originalSupportedClassEquiv A B P transport base hOne E
        i (σ (Quotient.mk'' i : C)) (hSup i)
    equivariant := by
      intro i g x
      exact originalSupportedClassMap_equivariant
        A B P transport base hOne E
        i (σ (Quotient.mk'' i : C)) (hSup i) g x
  }

end
end CCO.ExactEPGeometry
