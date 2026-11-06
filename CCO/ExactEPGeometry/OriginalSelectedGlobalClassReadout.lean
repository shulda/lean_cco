import CCO.ExactEPGeometry.OriginalSelectedFiniteReachedInjectivity
import CCO.ExactEPGeometry.OriginalSelectedGlobalEInjection

/-!
# B062 C90/C95: selected representatives retain their exact global E-class

The canonical map from ANY current point to the selected occupancy
quotient commutes with the actual global original E quotient. Thus
the reached representatives used in mixed finite marked charts
represent their prescribed selected E-points even in the GLOBAL
quotient, not merely as distinct real points or coarse K/E classes.

This discharges the old-E no-collapse premise of the actual successor
finite-chart theorem. No quotient SAP or action section is used.
-/

universe u v w t z

namespace CCO.ExactEPGeometry

open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- The actual selected occupancy point of any old current point
has precisely that point's global original E-class. -/
theorem originalCurrentToSelectedPoint_globalE
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    (p : Sigma B.Point) :
    (Quotient.mk'' (originalSelectedTaggedRepresentative
      A B P transport base hOne E
        (originalCurrentToSelectedPoint
          A B P transport base hOne E p)) :
      Quotient (currentOriginalExactSetoid A B P base hOne E)) =
    Quotient.mk'' p := by
  rcases p with ⟨i,x⟩
  let Occ := OriginalOccupancy A B P base hOne E
  let sigma := originalOccupancyRepresentativeEmbedding
    A B P base hOne E
  have hSup : (originalExactOccupancySetoid A B P base hOne E).r
      i (sigma (Quotient.mk'' i : Occ)) := by
    apply Quotient.exact
    exact (originalOccupancyRepresentative_class
      A B P base hOne E (Quotient.mk'' i : Occ)).symm
  let q := originalSupportedClassMap A B P transport base hOne E
    i (sigma (Quotient.mk'' i : Occ)) hSup (Quotient.mk'' x)
  change (Quotient.mk''
    (⟨sigma (Quotient.mk'' i : Occ),Quotient.out q⟩ : Sigma B.Point) :
      Quotient (currentOriginalExactSetoid A B P base hOne E)) =
    Quotient.mk'' (⟨i,x⟩ : Sigma B.Point)
  calc
    (Quotient.mk''
        (⟨sigma (Quotient.mk'' i : Occ),Quotient.out q⟩ : Sigma B.Point) :
          Quotient (currentOriginalExactSetoid A B P base hOne E)) =
        selectedOriginalClassToGlobal A B P transport base hOne E
          (sigma (Quotient.mk'' i : Occ))
          (Quotient.mk'' (Quotient.out q)) := rfl
    _ = selectedOriginalClassToGlobal A B P transport base hOne E
          (sigma (Quotient.mk'' i : Occ)) q :=
      congrArg (selectedOriginalClassToGlobal A B P transport base hOne E
        (sigma (Quotient.mk'' i : Occ))) (Quotient.out_eq q)
    _ = selectedOriginalClassToGlobal A B P transport base hOne E
          i (Quotient.mk'' x) :=
      originalSupportedClassMap_global A B P transport base hOne E
        i (sigma (Quotient.mk'' i : Occ)) hSup (Quotient.mk'' x)
    _ = Quotient.mk'' (⟨i,x⟩ : Sigma B.Point) := rfl

/-- The actual reached representative is in the SAME global
original E-class as the canonical selected representative. -/
theorem originalSelectedReachedRepresentative_globalE
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
          (Quotient.mk'' b.val : OriginalOccupancy A B P
            (P.parent r) (fun i => hOne (P.parent r) i) E)) :
    (Quotient.mk'' (⟨b.val,
      originalSelectedReachedEclassRepresentative
        A B P transport hOne Kroot E b q⟩ : Sigma B.Point) :
      Quotient (currentOriginalExactSetoid A B P (P.parent r)
        (fun i => hOne (P.parent r) i) E)) =
    Quotient.mk'' (originalSelectedTaggedRepresentative
      A B P transport (P.parent r)
        (fun i => hOne (P.parent r) i) E
          (⟨(Quotient.mk'' b.val : OriginalOccupancy A B P
            (P.parent r) (fun i => hOne (P.parent r) i) E),q⟩ :
              Sigma (originalExactSelectedQuotientCurrentSource
                A B P transport (P.parent r)
                  (fun i => hOne (P.parent r) i) E).Point)) := by
  let p : Sigma B.Point := ⟨b.val,
    originalSelectedReachedEclassRepresentative
      A B P transport hOne Kroot E b q⟩
  have h := originalCurrentToSelectedPoint_globalE
    A B P transport (P.parent r)
      (fun i => hOne (P.parent r) i) E p
  rw [originalSelectedReachedRepresentative_total_spec] at h
  exact h.symm

end
end CCO.ExactEPGeometry
