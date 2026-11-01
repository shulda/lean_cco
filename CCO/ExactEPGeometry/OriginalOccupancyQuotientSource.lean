import CCO.ExactEPGeometry.SelectedSortSource
import CCO.ExactEPGeometry.OriginalAllCurrentQuotientSource
import CCO.ExactEPGeometry.OriginalOccupancyRepresentatives

/-!
# B062 C67: REAL one-parent-per-occupancy E-quotient current source

Start with the already proved fully NAMED-SORTED simultaneous quotient
source of the ACTUAL current many-parent AP+HOM CCO prefix. Its carrier
on parent p is literally p/E|p² and the accepted typed I13 provider
proves finite orbital language, joint homogeneity, ordinary AP/JEP,
triangle fullness and semantic HOM CCO, without SAP.

The real occupancy equivalence partitions current parent names; each
component is a Quotient of those ACTUAL names and has a representative
parent chosen from that same component. Those chosen parents are
PAIRWISE DISTINCT. Restrict the already constructed all-parent
quotient source to that genuine INJECTIVE selection. The proved
selected-sort source lemma constructs a real CurrentSource with
complete inherited homogeneous orbital palette and HOM CCO. C66's
actual E-class occupancy theorem shows that its points represent
exactly the REAL global E-classes of each occupancy component.

This is the required actual quotient PREFIX, not an arbitrary
many-to-one renaming of duplicate sorts or a group action section.
No new quotient SAP, arbitrary mixed exact descent, hypothetical
CCO provider, fake identity diversity atom or unproved age.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter.Towers

noncomputable section

/-- A genuine actual representative of every current E-occupancy
class. Equality of representatives IMPLIES equality of classes
because they are the same literal original current sort name. -/
def originalOccupancyRepresentativeEmbedding
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base) :
    OriginalOccupancy A B P base hOne E ↪ B.Sorts where
  toFun := originalOccupancyRepresentative A B P base hOne E
  inj' := by
    intro c d h
    calc
      c = (Quotient.mk''
        (originalOccupancyRepresentative A B P base hOne E c) :
          OriginalOccupancy A B P base hOne E) :=
        (originalOccupancyRepresentative_class A B P base hOne E c).symm
      _ = (Quotient.mk''
        (originalOccupancyRepresentative A B P base hOne E d) :
          OriginalOccupancy A B P base hOne E) := congrArg Quotient.mk'' h
      _ = d :=
        originalOccupancyRepresentative_class A B P base hOne E d

/-- The occupancy-sort index is FINITE, since the true current
source has finitely many actual named sorts and every occupancy
class has a real representative. -/
theorem originalOccupancyFinite
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base) :
    Finite (OriginalOccupancy A B P base hOne E) := by
  letI : Fintype B.Sorts := B.source.finiteSort
  exact Finite.of_surjective
    (fun p : B.Sorts =>
      (Quotient.mk'' p : OriginalOccupancy A B P base hOne E))
    Quotient.mk''_surjective

/-- Actual homogeneous AP+HOM CCO quotient prefix with EXACTLY one
current parent sort per E-occupancy class, constructed by selecting
those names inside the PREVIOUSLY constructed full typed quotient
source. The quotient carrier of each named object is the literal
quotient of its selected current parent by E|p², and no other
possibly duplicate copy of that class is retained. -/
noncomputable def originalExactSelectedQuotientCurrentSource
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base) :
    CurrentSource.{u,v,v,t} := by
  letI : Finite (OriginalOccupancy A B P base hOne E) :=
    originalOccupancyFinite A B P base hOne E
  letI : Fintype (OriginalOccupancy A B P base hOne E) :=
    Fintype.ofFinite _
  let Q : CurrentSource.{u,v,v,t} :=
    originalExactAllCurrentQuotientCurrentSource
      A B P transport base hOne E
  exact selectedSortCurrentSource Q
    (originalOccupancyRepresentativeEmbedding A B P base hOne E)

/-- Each actual selected quotient source object c has exactly the
REAL local E-class carrier of its canonical occupancy parent;
there is no independent new copy or choice of a point in the class. -/
theorem originalExactSelectedQuotientPoint_eq
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    (c : OriginalOccupancy A B P base hOne E) :
    (originalExactSelectedQuotientCurrentSource A B P
      transport base hOne E).Point c =
      OriginalSelectedClass A B P transport base hOne E
        (originalOccupancyRepresentative A B P base hOne E c) := rfl

/-- All actual source C67 properties now belong to the REAL
occupancy-indexed complete current source itself, not an assumed
abstract source property or a phase-only seed quotient. -/
theorem originalExactSelectedQuotient_homogeneous
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base) :
    let Q := originalExactSelectedQuotientCurrentSource A B P
      transport base hOne E
    HomogeneousSource Q.source Q.G := by
  dsimp only
  exact (originalExactSelectedQuotientCurrentSource A B P
    transport base hOne E).homogeneous

theorem originalExactSelectedQuotient_cco
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base) :
    let Q := originalExactSelectedQuotientCurrentSource A B P
      transport base hOne E
    SemanticCCO.{u,v,max u v,v} Q.source := by
  dsimp only
  exact (originalExactSelectedQuotientCurrentSource A B P
    transport base hOne E).cco

end
end CCO.ExactEPGeometry
