import CCO.ExactEPGeometry.OriginalCoherentWordTI
import CCO.ExactEPGeometry.OriginalRetainedProjectedGateBase
import CCO.ExactEPGeometry.OriginalAllCurrentQuotientSource
import CCO.RigidGroupoid.Geometry.ProjectedKernels

/-!
# B062 C82: ACTUAL projected full exact gate before the next quotient step

For kernels e_p that are the restrictions of ONE original exact E,
the guarded source TP gives coherent typed word intertwining.
Consequently the simultaneous NAMED-SORTED quotient of the ACTUAL
current prefix can descend a current gate K_p with e_p <= K_p:
the image of the entire gate relation is a genuinely FULL RAW exact
quotient relation, not just a setoid or a union of orbitals.

For a retained original E <= G, the previous source theorem
discharges the nesting e_b <= K_b for EVERY active reached parent.
The resulting exactness applies BEFORE any subsequent safe
quotient step. No quotient SAP or automorphism group section.

This module concerns the genuine ALL-PARENT named quotient source.
Full-RAW exactness after selecting only one representative sort per
occupancy class is NOT inferred from arbitrary sort restriction,
which may remove necessary word-middle sorts. That remaining
selected-source transport is separately required for complete C82.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- For one original-E coherent kernel family, the image of ANY
genuine current exact gate K with actual e_p <= K is FULL exact
in the ALREADY CONSTRUCTED complete named-sorted quotient prefix.
Every RAW word uses the source-proved current typed TI. -/
theorem original_coherent_allparent_projected_gate_exact
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    (p : B.Sorts) (K : Kernel B.source p)
    (hNested : originalExactOnCurrentSort
      A B P transport base hOne E p ≤ current_kernel_exact_eq B K) :
    FullExact
      (originalExactAllCurrentQuotientCurrentSource
        A B P transport base hOne E).source
      (Quotient.image
        (fun x : B.Point p => (Quotient.mk'' x :
          (originalExactAllCurrentQuotientCurrentSource
            A B P transport base hOne E).Point p))
        (fun y : B.Point p => (Quotient.mk'' y :
          (originalExactAllCurrentQuotientCurrentSource
            A B P transport base hOne E).Point p))
        K.rel) := by
  let J := originalExactCurrentKernelFamily
    A B P transport base hOne E
  let W := originalExactCurrentKernelWords
    A B P transport base hOne E
  let e : ExactEq B.source p :=
    originalExactOnCurrentSort A B P transport base hOne E p
  let Ke : Kernel B.source p := ⟨e.val.val,e.property⟩
  have hSat : RawExact.saturate
      (RawExact.evaluate B.source (W p).words) K.rel
      (RawExact.evaluate B.source (W p).words) = K.rel := by
    have hW : RawExact.evaluate B.source (W p).words = Ke.rel :=
      originalExactCurrentKernelWords_relation
        A B P transport base hOne E p
    rw [hW]
    change TRel.comp (TRel.comp Ke.rel K.rel) Ke.rel = K.rel
    have hLe : Ke.setoid ≤ K.setoid := hNested
    rw [Ke.left_absorb hLe]
    exact Ke.right_absorb hLe
  obtain ⟨D,hD⟩ := K.exact
  have hSatD : RawExact.saturate
      (RawExact.evaluate B.source (W p).words)
      (RawExact.evaluate B.source D.words)
      (RawExact.evaluate B.source (W p).words) =
        RawExact.evaluate B.source D.words := by
    simpa only [hD] using hSat
  obtain ⟨F,hF⟩ := original_coherent_current_exact_descent
    A B P transport tp base hOne E D hSatD
  refine ⟨F,?_⟩
  calc
    RawExact.evaluate
        (originalExactAllCurrentQuotientCurrentSource
          A B P transport base hOne E).source F.words =
      CCO.ExactCRT.quotientRelation
        (CCO.ExactCRT.CanonicalTyped.projection J p)
        (CCO.ExactCRT.CanonicalTyped.projection J p)
        (RawExact.evaluate B.source D.words) := hF
    _ = Quotient.image
      (fun x : B.Point p => (Quotient.mk'' x :
        (originalExactAllCurrentQuotientCurrentSource
          A B P transport base hOne E).Point p))
      (fun y : B.Point p => (Quotient.mk'' y :
        (originalExactAllCurrentQuotientCurrentSource
          A B P transport base hOne E).Point p))
      K.rel := by
        rw [hD]
        rfl

/-- C82 genuine source-application, with NO added quotient gate
exactness premise: retained E <= original G and C56 together
prove e_b <= K_b for every member of the full original reached
groupoid; its projected gate is FULL RAW exact in the actual
all-parent quotient source before starting the next phase. -/
theorem original_retained_full_reached_projected_gate_exact_allparent
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
    let Q := originalExactAllCurrentQuotientCurrentSource A B P
      transport (P.parent r) (fun i => hOne (P.parent r) i) E
    FullExact Q.source
      (Quotient.image
        (fun x : B.Point b.val => (Quotient.mk'' x : Q.Point b.val))
        (fun y : B.Point b.val => (Quotient.mk'' y : Q.Point b.val))
        Kb.rel) := by
  dsimp only
  exact original_coherent_allparent_projected_gate_exact
    A B P transport tp (P.parent r)
    (fun i => hOne (P.parent r) i) E b.val
    (Reached.kernel B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) b)
    (original_retained_current_E_below_full_gate
      A B P transport tp hOne Kroot E hE b)

end
end CCO.ExactEPGeometry
