import CCO.ExactEPGeometry.OriginalRetainedSelectedArrowFunctor

/-!
# B062 C84: selected full Arrow identities and inverses are literal

The ACTUAL C83 all-current-to-selected E-quotient Hom equivalence is
already proved, and C84 now proves that it transports every full
source Arrow composition. To give a genuine full groupoid map rather
than a bare Hom bijection, we also verify whole gate identities and
inverse complete binary Arrow relations in the selected source.

The quotient identity is the WHOLE projected K_b/E_b gate relation,
not logical equality. The inverse relation retains every actual
displayed pair and its real endpoint types. These statements do
not require quotient SAP, a group automorphism section or an
unproved arbitrary mixed RAW reverse descent.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- Every genuine full Reached gate identity projects to the whole
selected-quotient gate identity, not the quotient logical diagonal. -/
theorem originalRetainedSelectedArrow_id
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (hOne : ∀ i j : A.Sorts, i = j)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (E : ExactEq A.source (P.parent r))
    (hE : E ≤ PrefixExactLargestLift.largest A B P transport tp r
      (current_kernel_exact_eq B Kroot))
    (b : Reached B.source Kroot) :
    let Kb := Reached.kernel B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) b
    (originalRetainedSelectedArrowEquiv A B P transport tp
      hOne Kroot E hE b b) (Arrow.id Kb) =
      Arrow.id
        (originalRetainedSelectedKernel A B P transport tp
          hOne Kroot E hE b) := by
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let Q : CurrentSource.{u,v,v,t} :=
    originalExactAllCurrentQuotientCurrentSource
      A B P transport base hBase E
  letI : ∀ i : Q.Sorts, MulAction B.G (Q.Point i) := Q.action
  let Occ := OriginalOccupancy A B P base hBase E
  letI : Finite Occ := originalOccupancyFinite A B P base hBase E
  letI : Fintype Occ := Fintype.ofFinite Occ
  let σ : Occ ↪ B.Sorts :=
    originalOccupancyRepresentativeEmbedding A B P base hBase E
  let D : SelectedRetyping (X := Q.Point) σ (G := B.G) :=
    originalSelectedSortRetyping A B P transport base hBase E
  let π : ∀ i : B.Sorts, B.Point i → Q.Point i :=
    fun _ x => Quotient.mk'' x
  let Kb := Reached.kernel B.homogeneous
    (exactCalculus_of_homogeneous_CCO
      B.source B.homogeneous B.cco) b
  apply Arrow.ext
  change D.transportRelation
      (Quotient.image (π b.val) (π b.val) Kb.rel) =
    D.transportRelation
      (Quotient.image (π b.val) (π b.val) Kb.rel)
  rfl

/-- The actual complete Hom bijections exchange source and target
correctly under the genuine inverse Arrow, on all reached objects
and every real projected endpoint, not just one chosen orbit. -/
theorem originalRetainedSelectedArrow_inv
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (hOne : ∀ i j : A.Sorts, i = j)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (E : ExactEq A.source (P.parent r))
    (hE : E ≤ PrefixExactLargestLift.largest A B P transport tp r
      (current_kernel_exact_eq B Kroot))
    (b c : Reached B.source Kroot)
    (R : Arrow B.source
      (Reached.kernel B.homogeneous
        (exactCalculus_of_homogeneous_CCO
          B.source B.homogeneous B.cco) b)
      (Reached.kernel B.homogeneous
        (exactCalculus_of_homogeneous_CCO
          B.source B.homogeneous B.cco) c)) :
    (originalRetainedSelectedArrowEquiv A B P transport tp
      hOne Kroot E hE c b) R.inv =
    ((originalRetainedSelectedArrowEquiv A B P transport tp
      hOne Kroot E hE b c) R).inv := by
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let Q : CurrentSource.{u,v,v,t} :=
    originalExactAllCurrentQuotientCurrentSource
      A B P transport base hBase E
  letI : ∀ i : Q.Sorts, MulAction B.G (Q.Point i) := Q.action
  let Occ := OriginalOccupancy A B P base hBase E
  letI : Finite Occ := originalOccupancyFinite A B P base hBase E
  letI : Fintype Occ := Fintype.ofFinite Occ
  let σ : Occ ↪ B.Sorts :=
    originalOccupancyRepresentativeEmbedding A B P base hBase E
  let D : SelectedRetyping (X := Q.Point) σ (G := B.G) :=
    originalSelectedSortRetyping A B P transport base hBase E
  let π : ∀ i : B.Sorts, B.Point i → Q.Point i :=
    fun _ x => Quotient.mk'' x
  apply Arrow.ext
  change D.transportRelation
      (Quotient.image (π c.val) (π b.val)
        (TRel.converse R.rel)) =
    TRel.converse
      (D.transportRelation
        (Quotient.image (π b.val) (π c.val) R.rel))
  rw [Quotient.image_converse, D.transportRelation_converse]

end
end CCO.ExactEPGeometry
