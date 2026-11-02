import CCO.ExactEPGeometry.OriginalSelectedFiniteRepresentatives
import CCO.APCharacter.Age.Category

/-!
# B062 C90: finite complete source charts from real selected quotient points

C67 provides an ACTUAL quotient prefix source. C90 now chooses real
old parent points representing all points of any ALREADY REALIZED
finite quotient configuration, without a section of group actions.
Their full old colour table is a genuine finite induced source chart
in the already accepted old-age category. It is NOT an arbitrary
fine witness with prescribed old atomic colours: only the chosen
old colours are recorded, while the quotient colours are recovered
by projecting their actual E-classes back.

Distinct original E-quotient vertices stay distinct in this old
chart. No hypothetical new marked source, quotient SAP, universal
realization of arbitrary locally allowed quotient diagrams or
extra external provider is assumed.
-/

universe u v w t z

namespace CCO.ExactEPGeometry

open APCharacter.Towers

noncomputable section

/-- The complete OLD source age chart of ANY finite DISTINCT actual
selected E-quotient points. This is the genuine induced finite chart
on their actual old point representatives. In particular the
identity-inclusive original pair colours are all recorded and no
synthetic representative colour is postulated. -/
noncomputable def originalSelectedFiniteOldChart
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    {V : Type z} [Finite V]
    (points : V ↪ Sigma
      (originalExactSelectedQuotientCurrentSource
        A B P transport base hOne E).Point) :
    APCharacter.Age.Chart B.source
      (APCharacter.Age.zeroMask B.source) :=
by
  classical
  -- The old-age chart interface uses a small finite vertex type.
  -- Relabel an arbitrary universe-polymorphic finite family by Fin n.
  letI : Fintype V := Fintype.ofFinite V
  let e : Fin (Fintype.card V) ≃ V := (Fintype.equivFin V).symm
  exact APCharacter.Age.oldChart B.source
    (fun v : Fin (Fintype.card V) =>
      originalSelectedTaggedRepresentative
        A B P transport base hOne E (points (e v)))
    ((originalSelectedFiniteRepresentative_injective
      A B P transport base hOne E points).comp e.injective)

/-- Reprojecting the ACTUAL chosen old points recovers the
precise selected quotient colour of the original two points.
The old representatives need not carry any prescribed old fine
atomic orbital; only their real quotient pair colour is fixed. -/
theorem originalSelectedRepresentative_pair_colour
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    (c d : OriginalOccupancy A B P base hOne E)
    (x : (originalExactSelectedQuotientCurrentSource
      A B P transport base hOne E).Point c)
    (y : (originalExactSelectedQuotientCurrentSource
      A B P transport base hOne E).Point d) :
    let Q := originalExactSelectedQuotientCurrentSource
      A B P transport base hOne E
    Q.source.colour x y =
      Q.source.colour
        (Quotient.mk'' (originalSelectedTaggedRepresentative
          A B P transport base hOne E ⟨c,x⟩).2)
        (Quotient.mk'' (originalSelectedTaggedRepresentative
          A B P transport base hOne E ⟨d,y⟩).2) := by
  let Q := originalExactSelectedQuotientCurrentSource
    A B P transport base hOne E
  have hx :
      (Quotient.mk'' (originalSelectedTaggedRepresentative
        A B P transport base hOne E ⟨c,x⟩).2 : Q.Point c) = x :=
    originalSelectedTaggedRepresentative_class
      A B P transport base hOne E ⟨c,x⟩
  have hy :
      (Quotient.mk'' (originalSelectedTaggedRepresentative
        A B P transport base hOne E ⟨d,y⟩).2 : Q.Point d) = y :=
    originalSelectedTaggedRepresentative_class
      A B P transport base hOne E ⟨d,y⟩
  change Q.source.colour x y =
    Q.source.colour
      (Quotient.mk'' (originalSelectedTaggedRepresentative
        A B P transport base hOne E ⟨c,x⟩).2)
      (Quotient.mk'' (originalSelectedTaggedRepresentative
        A B P transport base hOne E ⟨d,y⟩).2)
  rw [hx,hy]

end
end CCO.ExactEPGeometry
