import CCO.ExactEPGeometry.OriginalSelectedFiniteRepresentatives

/-!
# B062 C96: true selected quotient classes embed into the global old E quotient

The canonical selected E-quotient source has exactly one actual old
parent for each original E-occupancy class. Distinct selected quotient
points therefore represent DISTINCT global old E-classes, not merely
different tags or different old real representatives.

Proof uses only the genuine occupied-sort setoid and exact selected
per-sort full-E quotient; no quotient SAP, group-action section,
extra source hypothesis, or abstract quotient-point selector.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- The actual canonical old representative of any selected
E-quotient point gives an injective map to the WHOLE original
global E-class quotient. It is not merely injective as an old
real POINT (the earlier C90 theorem), but also after quotienting
the old entire tagged carrier by the true full original E. -/
theorem originalSelectedTaggedRepresentative_globalE_injective
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base) :
    Function.Injective (fun q : Sigma
      (originalExactSelectedQuotientCurrentSource
        A B P transport base hOne E).Point =>
        (Quotient.mk''
          (originalSelectedTaggedRepresentative
            A B P transport base hOne E q) :
          Quotient (currentOriginalExactSetoid
            A B P base hOne E))) := by
  intro a b hab
  rcases a with ⟨c,x⟩
  rcases b with ⟨d,y⟩
  let sigma : OriginalOccupancy A B P base hOne E → B.Sorts :=
    originalOccupancyRepresentative A B P base hOne E
  have hE : (currentOriginalExactSetoid A B P base hOne E).r
      (⟨sigma c, Quotient.out x⟩ : Sigma B.Point)
      (⟨sigma d, Quotient.out y⟩ : Sigma B.Point) := by
    exact Quotient.exact hab
  have hSupport : (originalExactOccupancySetoid
      A B P base hOne E).r (sigma c) (sigma d) := by
    exact ⟨Quotient.out x,Quotient.out y,hE⟩
  have hcd : c = d := by
    calc
      c = (Quotient.mk'' (sigma c) :
          OriginalOccupancy A B P base hOne E) :=
            (originalOccupancyRepresentative_class
              A B P base hOne E c).symm
      _ = (Quotient.mk'' (sigma d) :
          OriginalOccupancy A B P base hOne E) :=
            Quotient.sound hSupport
      _ = d :=
            originalOccupancyRepresentative_class
              A B P base hOne E d
  subst d
  have hLocal :
      originalExactOnCurrentSort
        A B P transport base hOne E (sigma c)
          (Quotient.out x) (Quotient.out y) :=
    (originalExactOnCurrentSort_iff
      A B P transport base hOne E (sigma c)
        (Quotient.out x) (Quotient.out y)).mpr hE
  have hxy : x = y := by
    calc
      x = (Quotient.mk'' (Quotient.out x) :
          (originalExactSelectedQuotientCurrentSource
            A B P transport base hOne E).Point c) :=
            (Quotient.out_eq x).symm
      _ = (Quotient.mk'' (Quotient.out y) :
          (originalExactSelectedQuotientCurrentSource
            A B P transport base hOne E).Point c) :=
            Quotient.sound hLocal
      _ = y := Quotient.out_eq y
  exact congrArg (Sigma.mk c) hxy

end
end CCO.ExactEPGeometry
