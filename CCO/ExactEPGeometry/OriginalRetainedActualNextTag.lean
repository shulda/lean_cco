import CCO.ExactEPGeometry.OriginalRetainedAnyMarkCorrection
import CCO.APCharacter.SourceAge.SingleStep

/-!
# B062 C94/C96: retained original E preserves every actual next child

In the TRUE constructed successor, the same-parent original E relation
preserves the actual child tag on EVERY old parent. On reached parents
this is the proved E-class constancy of ANY globally legal full-character
marking, applied to the actual marked-limit identification. On inactive
parents the genuine source mask has the single zero bit.

This supplies the child-sort condition needed when lifting complete old
E-saturated pair-block witnesses into the actual NEW quotient palette.
It does not assume a seed marking is homogeneous or a quotient has SAP.
-/

universe u v w t
namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.Towers
open APCharacter.SourceAge
open RigidGroupoid.Geometry

noncomputable section

/-- At a retained step, the original E restriction preserves the
ACTUAL next child tag of every old point, on active and inactive
parents alike. The actual marking is constructed by SingleStep. -/
theorem originalRetainedActualNextTag_eq_of_E
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
      (current_kernel_exact_eq B Kroot))
    (i : B.Sorts) (x y : B.Point i)
    (hxy : originalExactOnCurrentSort A B P transport
      (P.parent r) (fun j => hOne (P.parent r) j) E i x y) :
    UnarySource.tag (SingleStep.identification B phase) i x =
      UnarySource.tag (SingleStep.identification B phase) i y := by
  let I := SingleStep.identification B phase
  let mark := UnarySource.mark I
  have hMark : phase.masks.GlobalMarking mark :=
    UnarySource.global_marking I
  apply Subtype.ext
  change mark ⟨i,x⟩ = mark ⟨i,y⟩
  by_cases hi : Nonempty (Bridge B.source Kroot i)
  · exact originalRetainedAnyMarkAnchorEclassEq
      A B P transport tp hOne Kroot phase E hE mark hMark
        (⟨i,hi⟩ : Reached B.source Kroot) x y hxy
  · have hx : mark ⟨i,x⟩ = 0 := hMark.1 (⟨i,x⟩ : Sigma B.Point) hi
    have hy : mark ⟨i,y⟩ = 0 := hMark.1 (⟨i,y⟩ : Sigma B.Point) hi
    exact hx.trans hy.symm

end
end CCO.ExactEPGeometry
