import CCO.ExactEPGeometry.OriginalSelectedGlobalEInjection

/-!
# B062 C66/C96: ALL original global E-classes are genuine selected quotient points

The actual one-parent-per-occupancy selected exact quotient does not
merely inject into the whole old global E-class quotient. The real C49
every-class occupancy theorem and C66 canonical selected parent show
EVERY true original E-class has a selected quotient representative.

The resulting equivalence is the canonical literal class map; it is
not a choice of an automorphism section, a K/E gate quotient, or an
assumed quotient SAP/source finite-age equivalence.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- Each full original E-class of the true current source is hit by
the actual selected original-E quotient source. The same selected
parent is used for the original E-occupancy component of the class. -/
theorem originalSelectedTaggedRepresentative_globalE_surjective
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base) :
    Function.Surjective (fun q : Sigma
      (originalExactSelectedQuotientCurrentSource
        A B P transport base hOne E).Point =>
        (Quotient.mk''
          (originalSelectedTaggedRepresentative
            A B P transport base hOne E q) :
          Quotient (currentOriginalExactSetoid
            A B P base hOne E))) := by
  let Q := originalExactSelectedQuotientCurrentSource
    A B P transport base hOne E
  let Occ := OriginalOccupancy A B P base hOne E
  let sigma : Occ → B.Sorts :=
    originalOccupancyRepresentative A B P base hOne E
  let S := currentOriginalExactSetoid A B P base hOne E
  change ∀ z : Quotient S, ∃ q : Sigma Q.Point,
    (Quotient.mk'' (originalSelectedTaggedRepresentative
      A B P transport base hOne E q) : Quotient S) = z
  intro z
  induction z using Quotient.inductionOn with
  | _ p =>
    rcases p with ⟨i,x⟩
    let c : Occ := Quotient.mk'' i
    obtain ⟨q,hq⟩ :=
      originalClass_at_canonical_occupancy_parent
        A B P transport base hOne E c i x rfl
    refine ⟨(⟨c,q⟩ : Sigma Q.Point), ?_⟩
    have hmk :
        (Quotient.mk'' (⟨sigma c,Quotient.out q⟩ :
          Sigma B.Point) : Quotient S) =
        selectedOriginalClassToGlobal
          A B P transport base hOne E (sigma c)
            (Quotient.mk'' (Quotient.out q)) := rfl
    have hout :
        selectedOriginalClassToGlobal
          A B P transport base hOne E (sigma c)
            (Quotient.mk'' (Quotient.out q)) =
        selectedOriginalClassToGlobal
          A B P transport base hOne E (sigma c) q :=
      congrArg (selectedOriginalClassToGlobal
        A B P transport base hOne E (sigma c)) (Quotient.out_eq q)
    exact hmk.trans (hout.trans hq)

/-- True selected quotient points are precisely the full original
E-classes, across all current unary occupancy sorts, using only
the actual original E-class and chosen canonically supported parent. -/
noncomputable def originalSelectedGlobalEClassEquiv
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base) :
    Sigma (originalExactSelectedQuotientCurrentSource
      A B P transport base hOne E).Point ≃
    Quotient (currentOriginalExactSetoid A B P base hOne E) :=
  Equiv.ofBijective
    (fun q => (Quotient.mk'' (originalSelectedTaggedRepresentative
      A B P transport base hOne E q) :
      Quotient (currentOriginalExactSetoid A B P base hOne E)))
    ⟨originalSelectedTaggedRepresentative_globalE_injective
      A B P transport base hOne E,
     originalSelectedTaggedRepresentative_globalE_surjective
      A B P transport base hOne E⟩

/-- Pointwise form of the actual global original-E quotient
identification. Equality here is genuine E-class equality. -/
theorem originalSelectedGlobalEClassEquiv_apply
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    (q : Sigma (originalExactSelectedQuotientCurrentSource
      A B P transport base hOne E).Point) :
    originalSelectedGlobalEClassEquiv
      A B P transport base hOne E q =
      (Quotient.mk'' (originalSelectedTaggedRepresentative
        A B P transport base hOne E q) :
        Quotient (currentOriginalExactSetoid A B P base hOne E)) := rfl

end
end CCO.ExactEPGeometry
