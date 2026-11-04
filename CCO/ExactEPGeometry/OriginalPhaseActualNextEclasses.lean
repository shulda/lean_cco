import CCO.ExactEPGeometry.OriginalCurrentExactColourInvariance
import CCO.APCharacter.SourceAge.SingleStep

/-!
# B062 C96: original E-quotient classes do not collapse in a REAL marked successor

A true full fine-colour chart in an ACTUAL successor preserves and
reflects the original E-class matrix. A finite family of pairwise
distinct original E-classes therefore remains distinct after the
true current/next unary reduct composition.

The setoid is the actual global original E, NOT the marked limit's
logical equality or the coarser gate K/E. There is no quotient SAP,
automorphism group section or new projected atomic palette.
-/

universe u v w t z

namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- C96 old E-class pair matrix is preserved on ACTUAL new points,
using the real old-fine pair table and literal composite reduct. -/
theorem originalPhaseActualNextOriginalE_pairs_iff
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (phase : SourcePhase B.source B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) Kroot)
    {V : Type z}
    (old : V → Sigma B.Point)
    (next : V → Sigma (SingleStep.successor B phase).Point)
    (hFine : ∀ i j : V,
      taggedColour B.source (old i) (old j) =
        taggedColour B.source
          ((SingleStep.projection B phase).project (next i))
          ((SingleStep.projection B phase).project (next j))) :
    ∀ i j : V,
      (currentOriginalExactSetoid A B P base hOne E).r
        (old i) (old j) ↔
      (currentOriginalExactSetoid A (SingleStep.successor B phase)
        (P.compose (SingleStep.projection B phase))
        base hOne E).r (next i) (next j) := by
  have hPairs := originalCurrentExactE_fullColourChart_iff
    A B P base hOne E old
    (fun i => (SingleStep.projection B phase).project (next i)) hFine
  intro i j
  exact hPairs i j

/-- If the original old chart represents DIFFERENT true E-classes,
the actual successor chart represents DIFFERENT true E-classes,
not merely different real points or different coarse K-gate points. -/
theorem originalPhaseActualNextOriginalE_quotient_injective
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (phase : SourcePhase B.source B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) Kroot)
    {V : Type z}
    (old : V → Sigma B.Point)
    (next : V → Sigma (SingleStep.successor B phase).Point)
    (hFine : ∀ i j : V,
      taggedColour B.source (old i) (old j) =
        taggedColour B.source
          ((SingleStep.projection B phase).project (next i))
          ((SingleStep.projection B phase).project (next j)))
    (hOld : Function.Injective (fun i : V =>
      (Quotient.mk'' (old i) :
        Quotient (currentOriginalExactSetoid A B P base hOne E)))) :
    Function.Injective (fun i : V =>
      (Quotient.mk'' (next i) :
        Quotient (currentOriginalExactSetoid A
          (SingleStep.successor B phase)
          (P.compose (SingleStep.projection B phase))
          base hOne E))) := by
  intro i j hij
  apply hOld
  apply Quotient.sound
  have hNext :
      (currentOriginalExactSetoid A (SingleStep.successor B phase)
        (P.compose (SingleStep.projection B phase))
        base hOne E).r (next i) (next j) :=
    Quotient.exact hij
  exact (originalPhaseActualNextOriginalE_pairs_iff
    A B P base hOne E Kroot phase old next hFine i j).mpr hNext

end
end CCO.ExactEPGeometry
