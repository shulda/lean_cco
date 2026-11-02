import CCO.ExactEPGeometry.OriginalSelectedReachedPointLifts
import CCO.ExactEPGeometry.OriginalReachedOccupancyAnchors

/-!
# B062 C90/C95: original finite representatives remain distinct for distinct E-points

The TRUE canonical selected E-quotient point of an original current
point is defined by C66's actual equivariant all-parent-to-selected
carrier equivalence, not by a choice of a quotient group section.
The previously proved exact reached-point representative is a
right inverse ON LITERAL selected E-points. Therefore any finite
family of pairwise DISTINCT selected E-quotient points yields a
pairwise distinct old current point family, even when their original
reached occupancy sort names coincide or are represented by
different old current unary types.

No quotient SAP, artificial atom, altered source identity or new
surjectivity/coordinate hypothesis is added.
-/

universe u v w t z

namespace CCO.ExactEPGeometry

open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- The genuine ORIGINAL current point's literal selected E-quotient
point, on the one-per-original-E-occupancy selected quotient sort.
This map is total on ALL current sorts, reached or inactive. -/
noncomputable def originalCurrentToSelectedPoint
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base) :
    Sigma B.Point →
      Sigma (originalExactSelectedQuotientCurrentSource
        A B P transport base hOne E).Point := by
  let Qall : CurrentSource.{u,v,v,t} :=
    originalExactAllCurrentQuotientCurrentSource
      A B P transport base hOne E
  letI : ∀ i : Qall.Sorts, MulAction B.G (Qall.Point i) := Qall.action
  let Occ := OriginalOccupancy A B P base hOne E
  letI : Finite Occ := originalOccupancyFinite A B P base hOne E
  letI : Fintype Occ := Fintype.ofFinite Occ
  let sigma : Occ ↪ B.Sorts :=
    originalOccupancyRepresentativeEmbedding A B P base hOne E
  let D : SelectedRetyping (X := Qall.Point) sigma (G := B.G) :=
    originalSelectedSortRetyping A B P transport base hOne E
  exact fun p => ⟨(Quotient.mk'' p.1 : Occ),
    D.pointEquiv p.1 (Quotient.mk'' p.2)⟩

/-- The actual reached old representative of a specific selected
E-quotient point maps right back to that SAME point and named
selected sort, not just its full K/E gate class. -/
theorem originalSelectedReachedRepresentative_total_spec
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (hOne : ∀ i j : A.Sorts, i = j)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (E : ExactEq A.source (P.parent r))
    (b : Reached B.source Kroot)
    (q : (originalExactSelectedQuotientCurrentSource
      A B P transport (P.parent r)
      (fun i => hOne (P.parent r) i) E).Point
        (Quotient.mk'' b.val :
          OriginalOccupancy A B P (P.parent r)
          (fun i => hOne (P.parent r) i) E)) :
    originalCurrentToSelectedPoint A B P transport (P.parent r)
      (fun i => hOne (P.parent r) i) E
      ⟨b.val, originalSelectedReachedEclassRepresentative
        A B P transport hOne Kroot E b q⟩ =
      ⟨(Quotient.mk'' b.val :
          OriginalOccupancy A B P (P.parent r)
            (fun i => hOne (P.parent r) i) E), q⟩ := by
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let Qall : CurrentSource.{u,v,v,t} :=
    originalExactAllCurrentQuotientCurrentSource
      A B P transport base hBase E
  letI : ∀ i : Qall.Sorts, MulAction B.G (Qall.Point i) := Qall.action
  let Occ := OriginalOccupancy A B P base hBase E
  letI : Finite Occ := originalOccupancyFinite A B P base hBase E
  letI : Fintype Occ := Fintype.ofFinite Occ
  let sigma : Occ ↪ B.Sorts :=
    originalOccupancyRepresentativeEmbedding A B P base hBase E
  let D : SelectedRetyping (X := Qall.Point) sigma (G := B.G) :=
    originalSelectedSortRetyping A B P transport base hBase E
  change (⟨(Quotient.mk'' b.val : Occ),
      D.pointEquiv b.val (Quotient.mk''
        (originalSelectedReachedEclassRepresentative
          A B P transport hOne Kroot E b q))⟩ :
      Sigma (originalExactSelectedQuotientCurrentSource
        A B P transport base hBase E).Point) =
    ⟨(Quotient.mk'' b.val : Occ),q⟩
  exact congrArg (Sigma.mk (Quotient.mk'' b.val : Occ))
    (originalSelectedReachedEclassRepresentative_spec
      A B P transport hOne Kroot E b q)

/-- Source C90: if the ACTUAL selected quotient E-points are distinct
as tagged typed vertices, their old reached representatives are
distinct, independent of repeated gate K/E classes. -/
theorem originalSelectedFiniteReachedRepresentative_injective
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (hOne : ∀ i j : A.Sorts, i = j)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (E : ExactEq A.source (P.parent r))
    {V : Type z} [Finite V]
    (owners : V → OriginalReachedOccupancy
      A B P (P.parent r) (fun i => hOne (P.parent r) i) E Kroot)
    (point : ∀ v : V,
      (originalExactSelectedQuotientCurrentSource
        A B P transport (P.parent r)
        (fun i => hOne (P.parent r) i) E).Point
          (Quotient.mk'' (originalReachedOccupancyAnchor
            A B P (P.parent r)
              (fun i => hOne (P.parent r) i) E Kroot (owners v)).val))
    (hSelected : Function.Injective (fun v : V =>
      (⟨(Quotient.mk'' (originalReachedOccupancyAnchor
          A B P (P.parent r) (fun i => hOne (P.parent r) i)
          E Kroot (owners v)).val :
          OriginalOccupancy A B P (P.parent r)
            (fun i => hOne (P.parent r) i) E),point v⟩ :
        Sigma (originalExactSelectedQuotientCurrentSource
          A B P transport (P.parent r)
            (fun i => hOne (P.parent r) i) E).Point))) :
    Function.Injective (fun v : V =>
      (⟨(originalReachedOccupancyAnchor
          A B P (P.parent r) (fun i => hOne (P.parent r) i)
          E Kroot (owners v)).val,
        originalSelectedReachedEclassRepresentative
          A B P transport hOne Kroot E
          (originalReachedOccupancyAnchor
            A B P (P.parent r) (fun i => hOne (P.parent r) i)
            E Kroot (owners v)) (point v)⟩ : Sigma B.Point)) := by
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let anchor := originalReachedOccupancyAnchor
    A B P base hBase E Kroot
  let map : Sigma B.Point →
      Sigma (originalExactSelectedQuotientCurrentSource
        A B P transport base hBase E).Point :=
    originalCurrentToSelectedPoint A B P transport base hBase E
  intro i j hOld
  apply hSelected
  calc
    (⟨(Quotient.mk'' (anchor (owners i)).val :
        OriginalOccupancy A B P base hBase E),point i⟩ :
      Sigma (originalExactSelectedQuotientCurrentSource
        A B P transport base hBase E).Point) =
      map ⟨(anchor (owners i)).val,
        originalSelectedReachedEclassRepresentative
          A B P transport hOne Kroot E (anchor (owners i))
            (point i)⟩ :=
        (originalSelectedReachedRepresentative_total_spec
          A B P transport hOne Kroot E
            (anchor (owners i)) (point i)).symm
    _ = map ⟨(anchor (owners j)).val,
        originalSelectedReachedEclassRepresentative
          A B P transport hOne Kroot E (anchor (owners j))
            (point j)⟩ := congrArg map hOld
    _ = (⟨(Quotient.mk'' (anchor (owners j)).val :
        OriginalOccupancy A B P base hBase E),point j⟩ :
      Sigma (originalExactSelectedQuotientCurrentSource
        A B P transport base hBase E).Point) :=
        originalSelectedReachedRepresentative_total_spec
          A B P transport hOne Kroot E
            (anchor (owners j)) (point j)

end
end CCO.ExactEPGeometry
