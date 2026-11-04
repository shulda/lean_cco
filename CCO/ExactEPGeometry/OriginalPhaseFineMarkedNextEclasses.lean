import CCO.ExactEPGeometry.OriginalPhaseFineMarkedNextEmbedding
import CCO.ExactEPGeometry.OriginalPhaseActualNextEclasses

/-!
# B062 C96: true global E-class injection in the actual marked successor

A complete fine OLD marked chart in the genuine AP-only limit,
together with DISTINCT original global E-classes among its vertices,
produces a true finite successor-point diagram. It preserves every
child owner/phase bit and the entire old fine-colour table, reflects
the original E relation on all pairs, and remains injective AFTER
taking the true original E quotient of the actual successor.

The original E quotient, not the K/E gate quotient, is used here.
This is a source-level finite chart ingredient; it does not identify
the entire NEW marked quotient atomic palette or its finite age.
-/

universe u v w t z

namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.Towers
open APCharacter.SourceAge
open RigidGroupoid.Geometry
open OwnerTransversal.CountableColour

noncomputable section

/-- A real full marked-old-colour chart with distinct global E-classes
gives one genuine next-source chart with exactly the same old E-class
equality matrix and no collapse of quotient vertices. -/
theorem originalPhaseFineMarkedChart_nextOriginalEclasses
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (phase : SourcePhase B.source B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) Kroot)
    {V : Type z}
    (old : V → Sigma B.Point) (bits : V → ZMod 2)
    (f : V ↪ phase.MarkedLimit B.cco)
    (hOwner : ∀ v,
      (phase.markedCoding B.cco).table.owner (f v) =
        Age.ownerEquiv B.source ((old v).1,bits v))
    (hColour : ∀ v w,
      (phase.markedCoding B.cco).table.colour (f v) (f w) =
        Age.colourEquiv B.source
          (taggedColour B.source (old v) (old w)))
    (hOldDistinct : Function.Injective
      (fun v : V => (Quotient.mk'' (old v) :
        Quotient (currentOriginalExactSetoid A B P base hOne E)))) :
    ∃ next : V ↪ Sigma (SingleStep.successor B phase).Point,
      (∀ v,
        UnarySource.childLabel (SingleStep.identification B phase)
          (next v).1 = ((old v).1,bits v)) ∧
      (∀ v w,
        taggedColour B.source
          ((SingleStep.projection B phase).project (next v))
          ((SingleStep.projection B phase).project (next w)) =
        taggedColour B.source (old v) (old w)) ∧
      (∀ v w,
        (currentOriginalExactSetoid A B P base hOne E).r
          (old v) (old w) ↔
        (currentOriginalExactSetoid A
          (SingleStep.successor B phase)
          (P.compose (SingleStep.projection B phase))
          base hOne E).r (next v) (next w)) ∧
      Function.Injective
        (fun v : V => (Quotient.mk'' (next v) :
          Quotient (currentOriginalExactSetoid A
            (SingleStep.successor B phase)
            (P.compose (SingleStep.projection B phase))
            base hOne E))) := by
  obtain ⟨next,hBits,hFine⟩ :=
    originalPhaseFineMarkedChart_nextEmbedding
      B Kroot phase old bits f hOwner hColour
  have hOldFine : ∀ i j : V,
      taggedColour B.source (old i) (old j) =
        taggedColour B.source
          ((SingleStep.projection B phase).project (next i))
          ((SingleStep.projection B phase).project (next j)) :=
    fun i j => (hFine i j).symm
  refine ⟨next,hBits,hFine,?_,?_⟩
  · exact originalPhaseActualNextOriginalE_pairs_iff
      A B P base hOne E Kroot phase old next hOldFine
  · exact originalPhaseActualNextOriginalE_quotient_injective
      A B P base hOne E Kroot phase old next hOldFine hOldDistinct

end
end CCO.ExactEPGeometry
