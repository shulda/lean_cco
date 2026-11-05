import CCO.ExactEPGeometry.OriginalRetainedMixedSelectedChart
import CCO.ExactEPGeometry.OriginalRetainedMixedSelectedEclasses
import CCO.ExactEPGeometry.OriginalPhaseFineMarkedNextEclasses
import CCO.ExactEPGeometry.OriginalCurrentExactSaturatedColour

/-!
# B062 C95: real mixed quotient diagrams survive in the actual successor

For any distinct selected quotient vertices with the full retained
character masks and genuinely inactive remaining vertices, construct
ONE finite chart in the TRUE SingleStep successor. Its original E-classes
are distinct, its child bits and every old fine pair colour are correct,
and ALL original E-saturated old atomic blocks are preserved/reflected.

The global-E no-collapse premise is proved from the actual selected
quotient points, not supplied as an extra provider. This is the source
C95 finite-witness step, after the C89 old quotient realization. The NEW
quotient orbital palette and reverse finite-age assertion remain separate.
-/

universe u v w t z
namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.Towers
open APCharacter.SourceAge
open RigidGroupoid.Geometry
open CategoryTheory
open OwnerTransversal.CountableColour

noncomputable section

/-- A full finite actual selected-quotient marked diagram has a
true next-source realization without collapse of distinct E-classes.
No quotient SAP or additional E-distinctness premise is used. -/
theorem originalRetainedMixedSelectedMasks_actualNextQuotientChart
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (hOne : ∀ i j : A.Sorts, i = j)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (phase : SourcePhase B.source B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) Kroot)
    (E : ExactEq A.source (P.parent r))
    (hE : E ≤ PrefixExactLargestLift.largest A B P transport tp r
      (current_kernel_exact_eq B Kroot)) :
    let base := P.parent r
    let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
    let Occ := OriginalReachedOccupancy A B P base hBase E Kroot
    letI := originalRetainedOccupancyGroupoid
      A B P transport tp hOne Kroot E hE
    let Q := originalExactSelectedQuotientCurrentSource
      A B P transport base hBase E
    let anchor := originalReachedOccupancyAnchor
      A B P base hBase E Kroot
    let K := fun o : Occ => originalRetainedSelectedKernel
      A B P transport tp hOne Kroot E hE (anchor o)
    let chi := originalRetainedSelectedOccupancyCharacter
      A B P transport tp hOne Kroot phase E hE
    ∀ (n m : Nat)
      (owners : Fin n → Occ)
      (points : ∀ i : Fin n,
        Q.Point (Quotient.mk'' (anchor (owners i)).val))
      (bits : Fin n → ZMod 2),
      (∀ i j : Fin n,
        originalSelectedCompleteAtomicMask Q
          (K (owners i)) (K (owners j))
          (fun (R : owners i ⟶ owners j) => chi.value R)
          (Q.source.colour (points i) (points j))
          (bits i) (bits j)) →
      ∀ (inactivePoints : Fin m → Sigma Q.Point),
        Function.Injective (fun v : Sum (Fin n) (Fin m) =>
          match v with
          | Sum.inl i =>
              (⟨(Quotient.mk'' (anchor (owners i)).val :
                OriginalOccupancy A B P base hBase E),points i⟩ :
                Sigma Q.Point)
          | Sum.inr j => inactivePoints j) →
        (∀ j : Fin m,
          ¬Nonempty (Bridge B.source Kroot
            (originalSelectedTaggedRepresentative
              A B P transport base hBase E (inactivePoints j)).1)) →
        let old : Sum (Fin n) (Fin m) → Sigma B.Point :=
          fun v => match v with
          | Sum.inl i =>
              ⟨(anchor (owners i)).val,
                originalSelectedReachedEclassRepresentative
                  A B P transport hOne Kroot E
                    (anchor (owners i)) (points i)⟩
          | Sum.inr j =>
              originalSelectedTaggedRepresentative
                A B P transport base hBase E (inactivePoints j)
        let allBits : Sum (Fin n) (Fin m) → ZMod 2 :=
          fun v => match v with
          | Sum.inl i => bits i
          | Sum.inr _ => 0
        ∃ next : Sum (Fin n) (Fin m) ↪
            Sigma (SingleStep.successor B phase).Point,
          (∀ v, UnarySource.childLabel (SingleStep.identification B phase)
            (next v).1 = ((old v).1,allBits v)) ∧
          (∀ v w, taggedColour B.source
            ((SingleStep.projection B phase).project (next v))
            ((SingleStep.projection B phase).project (next w)) =
              taggedColour B.source (old v) (old w)) ∧
          (∀ v w, (currentOriginalExactSetoid A B P base hBase E).r
            (old v) (old w) ↔
            (currentOriginalExactSetoid A (SingleStep.successor B phase)
              (P.compose (SingleStep.projection B phase))
              base hBase E).r (next v) (next w)) ∧
          Function.Injective (fun v : Sum (Fin n) (Fin m) =>
            (Quotient.mk'' (next v) :
              Quotient (currentOriginalExactSetoid A
                (SingleStep.successor B phase)
                (P.compose (SingleStep.projection B phase))
                base hBase E))) ∧
          (∀ (a : Age.Colour B.source) (v w : Sum (Fin n) (Fin m)),
            originalCurrentExactSaturatedColour A B P base hBase E
              a (old v) (old w) ↔
            originalCurrentExactSaturatedColour A B P base hBase E
              a ((SingleStep.projection B phase).project (next v))
                ((SingleStep.projection B phase).project (next w))) := by
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let Occ := OriginalReachedOccupancy A B P base hBase E Kroot
  letI : Groupoid Occ :=
    originalRetainedOccupancyGroupoid
      A B P transport tp hOne Kroot E hE
  let Q := originalExactSelectedQuotientCurrentSource
    A B P transport base hBase E
  let anchor := originalReachedOccupancyAnchor
    A B P base hBase E Kroot
  dsimp only
  intro n m owners points bits hMasks inactivePoints hSelected hInactive
  let old : Sum (Fin n) (Fin m) → Sigma B.Point :=
    fun v => match v with
    | Sum.inl i =>
        ⟨(anchor (owners i)).val,
          originalSelectedReachedEclassRepresentative
            A B P transport hOne Kroot E
              (anchor (owners i)) (points i)⟩
    | Sum.inr j =>
        originalSelectedTaggedRepresentative
          A B P transport base hBase E (inactivePoints j)
  let allBits : Sum (Fin n) (Fin m) → ZMod 2 :=
    fun v => match v with
    | Sum.inl i => bits i
    | Sum.inr _ => 0
  obtain ⟨f,hOwner,hColour⟩ :=
    originalRetainedMixedSelectedMasks_oldMarkedChart
      A B P transport tp hOne Kroot phase E hE
        n m owners points bits hMasks inactivePoints hSelected hInactive
  have hOldDistinct : Function.Injective
      (fun v : Sum (Fin n) (Fin m) => (Quotient.mk'' (old v) :
        Quotient (currentOriginalExactSetoid A B P base hBase E))) :=
    originalRetainedMixedSelectedOld_globalE_injective
      A B P transport hOne Kroot E
        n m owners points inactivePoints hSelected
  obtain ⟨next,hBits,hFine,hEpairs,hDistinct⟩ :=
    originalPhaseFineMarkedChart_nextOriginalEclasses
      A B P base hBase E Kroot phase old allBits
        f hOwner hColour hOldDistinct
  refine ⟨next,hBits,hFine,hEpairs,hDistinct,?_⟩
  intro a v w
  exact originalCurrentExactSaturatedColour_taggedColour_iff
    A B P base hBase E a (old v) (old w)
      ((SingleStep.projection B phase).project (next v))
      ((SingleStep.projection B phase).project (next w))
      (hFine v w).symm

end
end CCO.ExactEPGeometry
