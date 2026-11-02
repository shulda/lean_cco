import CCO.UnaryTermsReturn.FiniteNormalCodes

/-!
# B052 C11–C13: each ACTUAL named term value has one finite normal code

This is the missing evaluation bridge between B049's actual
FULL old RAW term normalisation and the new B052 fixed finite
uniform normal-code family. Every named term, of arbitrary
finite syntax length and any genuine typed original target
sort, is evaluated at a real source point by its canonical
normal datum. Its target tag is the LITERAL old transported
FULL equivalence, shown equal to the term's named target.

Thus the actual one-generated ambient unary values are
included in an image of a FIXED finite code type, independent
of the input point and of term length; no image of arbitrary
total-unary partial-source data is asserted. Source-to-hidden
projection starts at a genuinely named original MI coordinate.
-/

universe u v w t

namespace CCO.UnaryTermsReturn

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

open CCO.TransitionClosure
open CCO.ParityHasse.Original

/-- Every actual real-source projection followed by one
arbitrarily long named quotient term has exactly the value
of SOME original finite RAW normal code. The target is
tagged by its actual old sort AND the full equivalence
kernel, not by an independently chosen hidden chart. -/
theorem original_real_named_term_value_has_normal_code
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    {i j : ι}
    (D : OriginalNamedHiddenCoordinate S H i)
    (F : OriginalNamedHiddenCoordinate S H j)
    (w : OriginalNamedRawUnaryTerm S H sap nr2 D F)
    (x : X i) :
    ∃ c : OriginalSourceNormalCode S (G := G) i,
      originalSourceNormalCodeValue S H x c =
        (⟨j,⟨F.val,
          OriginalNamedRawUnaryTerm.eval S H sap nr2 w
            (Quotient.mk D.val.val x)⟩⟩ :
              OriginalNormalCodeTargetValue S) := by
  obtain ⟨N, hSource, hTarget, hEdge⟩ :=
    OriginalOldUnaryWord.normal_relation S H
      (OriginalNamedRawUnaryTerm.toOld S H sap nr2 w)
  let T := originalCanonicalRawTransitionDatum_transport S H N.val.2
  obtain ⟨y,hxy⟩ := T.serial x
  have hNormal :=
    originalCanonicalUnaryNormalDatum_real_edge S H N x y hxy
  have hWord :=
    hEdge x y hxy
  change OriginalNamedRawUnaryTerm.eval S H sap nr2 w
      (Quotient.mk D.val.val x) =
        Quotient.mk F.val.val y at hWord
  refine ⟨⟨j,N⟩, ?_⟩
  change
    (⟨j,⟨originalTransportTargetColourEq S H N.val.2.val.1 T,
      (originalCanonicalUnaryNormalDatum_function S H N).2.2
        (Quotient.mk N.val.1.val x)⟩⟩ :
      OriginalNormalCodeTargetValue S) =
    (⟨j,⟨F.val,
      OriginalNamedRawUnaryTerm.eval S H sap nr2 w
        (Quotient.mk D.val.val x)⟩⟩ :
      OriginalNormalCodeTargetValue S)
  rw [hNormal, hWord, hTarget]

end CCO.UnaryTermsReturn
