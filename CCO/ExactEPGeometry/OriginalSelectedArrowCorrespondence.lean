import CCO.ExactEPGeometry.SelectedSortArrowReverse
import CCO.ExactEPGeometry.OriginalCoherentAllparentGroupoid
import CCO.ExactEPGeometry.OriginalSelectedSortRetyping

/-!
# B062 C83: ACTUAL original/current to selected E-quotient Hom equivalence

The full original-E all-parent quotient is an actual homogeneous
AP/HOM-CCO CurrentSource. Its projected complete exact K/e gates
and entire Arrow Hom sets have already been proved exactly equivalent
to the old current source via the accepted true endpoint provider.

C82's actual E-occupancy quotient retains one real local quotient
carrier per original E-occupancy component. The C49/C66 classwise
coverage and concrete B.G-equivariance prove genuine carrier
bijections, now used by the independently proved complete
SelectedRetyping.transportArrowEquiv (including its reverse direction).

Composing these two actual equivalences gives the FULL C83
correspondence of EVERY genuine old Arrow and EVERY genuine
selected-quotient Arrow between the literal transported projected
gates; no missing selected word-middle sort, quotient SAP,
assumed group section or conditional projected exactness.
Additional identification of duplicate source OBJECTS and the
corrected phase character belong to the following C84 stage.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- C83: real source-to-selected-quotient equivalence of ALL complete
Arrow Hom sets for arbitrary original-E nested exact gates at the
two displayed true current types. The target is the ACTUAL
one-representative-per-E-occupancy AP/HOM-CCO CurrentSource and its
genuine full-exact projected kernels, not an abstract oracle. -/
noncomputable def originalCoherentSelectedArrowEquiv
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    {p q : B.Sorts} (Kp : Kernel B.source p)
    (Kq : Kernel B.source q)
    (hp : originalExactOnCurrentSort A B P transport
      base hOne E p ≤ current_kernel_exact_eq B Kp)
    (hq : originalExactOnCurrentSort A B P transport
      base hOne E q ≤ current_kernel_exact_eq B Kq) :
    let Q := originalExactAllCurrentQuotientCurrentSource
      A B P transport base hOne E
    letI : ∀ i : Q.Sorts, MulAction B.G (Q.Point i) := Q.action
    let D := originalSelectedSortRetyping A B P transport base hOne E
    Arrow B.source Kp Kq ≃
      Arrow (originalExactSelectedQuotientCurrentSource
        A B P transport base hOne E).source
        (D.transportKernel Q.homogeneous
          (originalCoherentAllparentProjectedKernel
            A B P transport tp base hOne E p Kp hp))
        (D.transportKernel Q.homogeneous
          (originalCoherentAllparentProjectedKernel
            A B P transport tp base hOne E q Kq hq)) := by
  let Q : CurrentSource.{u,v,v,t} :=
    originalExactAllCurrentQuotientCurrentSource
      A B P transport base hOne E
  letI : ∀ i : Q.Sorts, MulAction B.G (Q.Point i) := Q.action
  let C := OriginalOccupancy A B P base hOne E
  letI : Finite C := originalOccupancyFinite A B P base hOne E
  letI : Fintype C := Fintype.ofFinite C
  let σ : C ↪ B.Sorts :=
    originalOccupancyRepresentativeEmbedding A B P base hOne E
  let D : SelectedRetyping (X := Q.Point) σ (G := B.G) :=
    originalSelectedSortRetyping A B P transport base hOne E
  let KpQ : Kernel Q.source p :=
    originalCoherentAllparentProjectedKernel
      A B P transport tp base hOne E p Kp hp
  let KqQ : Kernel Q.source q :=
    originalCoherentAllparentProjectedKernel
      A B P transport tp base hOne E q Kq hq
  change Arrow B.source Kp Kq ≃
    Arrow (selectedSortAtomicSource Q.source σ)
      (D.transportKernel Q.homogeneous KpQ)
      (D.transportKernel Q.homogeneous KqQ)
  exact (originalCoherentAllparentArrowEquiv
    A B P transport tp base hOne E Kp Kq hp hq).trans
    (D.transportArrowEquiv Q.homogeneous Q.cco KpQ KqQ)

end
end CCO.ExactEPGeometry
