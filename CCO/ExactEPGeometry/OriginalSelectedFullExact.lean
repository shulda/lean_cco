import CCO.ExactEPGeometry.OriginalSelectedSortRetyping

/-!
# B062 C82: FULL RAW exactness transported into the actual selected quotient

The all-parent simultaneous original-E quotient is an ACTUAL
homogeneous AP+HOM-CCO source. The selected quotient is an ACTUAL
one-representative-per-E-occupancy sort restriction of that source.
Simply restricting a RAW word may lose old intermediate sorts.

The source-proved equivariant bijection of EVERY all-parent E-class
sort with its chosen occupancy representative transports EACH
intermediate witness, full atomic orbital, and genuine equality
letter. The generic exact RAW retyping theorem therefore applies
to EVERY old full-exact relation and yields a complete nonempty
RAW presentation in the real selected quotient source.

This theorem gives full source-level C82 exactness transportation,
not an unproved quotient SAP property, action section, or assumed
preservation under deletion of intermediate sort names.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- C82 selected source: the EXACT transported image of ANY genuine
all-parent full-RAW-exact relation is full-RAW-exact in the ACTUAL
occupancy-selected quotient source, with all literal intermediate
sort witnesses and nonempty old evaluation retained. -/
theorem original_selected_full_exact_of_allparent
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    {i j : B.Sorts}
    (R : TRel (originalExactAllCurrentQuotientCurrentSource
      A B P transport base hOne E).Point i j)
    (hR : FullExact
      (originalExactAllCurrentQuotientCurrentSource
        A B P transport base hOne E).source R) :
    let Q := originalExactAllCurrentQuotientCurrentSource
      A B P transport base hOne E
    letI : ∀ k : Q.Sorts, MulAction B.G (Q.Point k) := Q.action
    let D := originalSelectedSortRetyping
      A B P transport base hOne E
    FullExact
      (originalExactSelectedQuotientCurrentSource
        A B P transport base hOne E).source
      (fun x y =>
        R ((D.pointEquiv i).symm x) ((D.pointEquiv j).symm y)) := by
  let Q : CurrentSource.{u,v,v,t} :=
    originalExactAllCurrentQuotientCurrentSource
      A B P transport base hOne E
  letI : ∀ k : Q.Sorts, MulAction B.G (Q.Point k) := Q.action
  let C := OriginalOccupancy A B P base hOne E
  let σ : C ↪ B.Sorts :=
    originalOccupancyRepresentativeEmbedding A B P base hOne E
  letI : Finite C := originalOccupancyFinite A B P base hOne E
  letI : Fintype C := Fintype.ofFinite C
  let D := originalSelectedSortRetyping
    A B P transport base hOne E
  change FullExact (selectedSortAtomicSource Q.source σ)
    (fun x y => R ((D.pointEquiv i).symm x) ((D.pointEquiv j).symm y))
  exact D.retypeFullExact Q.homogeneous R hR

end
end CCO.ExactEPGeometry
