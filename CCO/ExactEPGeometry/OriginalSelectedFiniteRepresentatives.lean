import CCO.ExactEPGeometry.OriginalOccupancyQuotientSource
import CCO.Finite

/-!
# B062 C89–C90: actual finite selected E-quotient representatives

The preceding C67 theorem constructs a GENUINE homogeneous AP+HOM
CCO CurrentSource with exactly one named parent per original E-support
class. Its points are the literal quotients of current old points
on the selected parent by the true original E restriction.

An arbitrary FINITE family of points already realized in this
selected quotient source can be lifted to a finite induced diagram
on real old points: choose actual representatives using Quotient.out
at the ACTUAL selected parent. Different E-classes remain distinct
and no real quotient pair orbital is changed when these witnesses
are reprojected. This is the C90 representative-selection step,
after a legal unmarked prefix has already been realized (C89).

It does NOT turn an arbitrary locally legal new diagram into a
realized quotient-prefix diagram, assert old atomic colour
preservation under arbitrary choice of representatives, assume
SAP of the quotient, or supply an automorphism group section.
Those real marked-age and source-induction obligations remain open.
-/

universe u v w t z

namespace CCO.ExactEPGeometry

open APCharacter.Towers

noncomputable section

/-- Choose an ACTUAL old current point representing each actual
selected quotient E-class on its TRUE canonical current parent
sort. This is a set-theoretic witness, NOT a group-equivariant
choice of representatives or a homogeneity/quotient section. -/
noncomputable def originalSelectedTaggedRepresentative
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    (q : Sigma (originalExactSelectedQuotientCurrentSource
      A B P transport base hOne E).Point) : Sigma B.Point :=
  ⟨originalOccupancyRepresentative A B P base hOne E q.1,
    Quotient.out q.2⟩

/-- The chosen point lies in PRECISELY its prescribed real E-class.
The quotient logical identity is E, never original logical equality. -/
theorem originalSelectedTaggedRepresentative_class
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    (q : Sigma (originalExactSelectedQuotientCurrentSource
      A B P transport base hOne E).Point) :
    (Quotient.mk'' (originalSelectedTaggedRepresentative
      A B P transport base hOne E q).2 :
        (originalExactSelectedQuotientCurrentSource
          A B P transport base hOne E).Point q.1) = q.2 := by
  change Quotient.mk'' (Quotient.out q.2) = q.2
  exact Quotient.out_eq q.2

/-- Distinct actual E-quotient points of one selected parent admit
old representatives that are REALLY E-INEQUIVALENT: collapsing
their different formal vertices under an old embedding is forbidden. -/
theorem originalSelectedRepresentatives_separate_E
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    (c : OriginalOccupancy A B P base hOne E)
    (x y : (originalExactSelectedQuotientCurrentSource
      A B P transport base hOne E).Point c)
    (hxy : x ≠ y) :
    ¬ originalExactOnCurrentSort A B P transport base hOne E
      (originalOccupancyRepresentative A B P base hOne E c)
      (Quotient.out x) (Quotient.out y) := by
  intro h
  apply hxy
  have hh :
      (Quotient.mk'' (Quotient.out x) :
        (originalExactSelectedQuotientCurrentSource
          A B P transport base hOne E).Point c) =
      (Quotient.mk'' (Quotient.out y) :
        (originalExactSelectedQuotientCurrentSource
          A B P transport base hOne E).Point c) := Quotient.sound h
  exact hxy (by simpa only [Quotient.out_eq] using hh)

/-- The real chosen representatives distinguish ALL selected
quotient points, including points in different occupancy named
sorts. This relies on the ACTUAL injective parent selection,
not on an arbitrary collapse of the old sort labels. -/
theorem originalSelectedTaggedRepresentative_injective
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base) :
    Function.Injective (originalSelectedTaggedRepresentative
      A B P transport base hOne E) := by
  intro p q hpq
  rcases p with ⟨c,x⟩
  rcases q with ⟨d,y⟩
  let sigma := originalOccupancyRepresentativeEmbedding
    A B P base hOne E
  have hcd : c = d := sigma.injective (congrArg Sigma.fst hpq)
  subst d
  have hxy : Quotient.out x = Quotient.out y := by
    change (⟨sigma c, Quotient.out x⟩ : Sigma B.Point) =
      ⟨sigma c, Quotient.out y⟩ at hpq
    simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using hpq
  have hclass : x = y := by
    have hh :
        (Quotient.mk'' (Quotient.out x) :
          (originalExactSelectedQuotientCurrentSource
            A B P transport base hOne E).Point c) =
        (Quotient.mk'' (Quotient.out y) :
          (originalExactSelectedQuotientCurrentSource
            A B P transport base hOne E).Point c) :=
      congrArg (fun a : B.Point (sigma c) =>
        (Quotient.mk'' a :
          (originalExactSelectedQuotientCurrentSource
            A B P transport base hOne E).Point c)) hxy
    simpa only [Quotient.out_eq] using hh
  exact congrArg (Sigma.mk c) hclass

/-- From ANY finite family of already REALIZED selected quotient
points, take its full induced source diagram on actual old current
representatives. The old diagram is finite, and its entire original
atomic table is inherited automatically from the genuine source. -/
noncomputable def originalSelectedFiniteRepresentativeDiagram
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    {V : Type z} [Finite V]
    (points : V → Sigma (originalExactSelectedQuotientCurrentSource
      A B P transport base hOne E).Point) :
    FiniteInduced (X := B.Point) where
  vertices := Set.range
    (fun v => originalSelectedTaggedRepresentative
      A B P transport base hOne E (points v))
  finite_vertices := Set.finite_range _

/-- When the finite quotient diagram has DISTINCT actual points,
its real representatives remain distinct. In particular no
two different E-classes were spuriously identified by lifting. -/
theorem originalSelectedFiniteRepresentative_injective
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    {V : Type z} [Finite V]
    (points : V ↪ Sigma (originalExactSelectedQuotientCurrentSource
      A B P transport base hOne E).Point) :
    Function.Injective
      (fun v : V => originalSelectedTaggedRepresentative
        A B P transport base hOne E (points v)) :=
  (originalSelectedTaggedRepresentative_injective
    A B P transport base hOne E).comp points.injective

end
end CCO.ExactEPGeometry
