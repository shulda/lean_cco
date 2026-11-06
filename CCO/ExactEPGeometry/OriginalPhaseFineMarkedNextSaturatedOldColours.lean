import CCO.ExactEPGeometry.OriginalCurrentExactSaturatedColour
import CCO.ExactEPGeometry.OriginalPhaseFineMarkedNextEmbedding

/-!
# B062 C96: complete E-saturated OLD orbital diagram in genuine next source

An actual complete fine OLD marked source chart embedded in the
constructed AP-only limit induces an injective family of ACTUAL
SingleStep successor points, preserving the genuine child names
and the complete OLD current atom-colour matrix. Hence for every
old current B atomic pair name, its TRUE original-E bisaturation
is preserved on every pair of the diagram.

No quotient SAP, atom name for the NEW marked quotient,
group-action section or full next quotient finite-age converse.
-/

universe u v w t z
namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.Towers
open APCharacter.SourceAge
open RigidGroupoid.Geometry
open OwnerTransversal.CountableColour

noncomputable section

/-- C96 forward OLD saturated orbital diagram transfer across
the constructed marked limit and genuine next source. The
E-saturated predicate is actual E;B-atom;E, not the complete
new marked quotient atomic palette. -/
theorem originalPhaseFineMarkedChart_nextSaturatedOldColours
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
          (taggedColour B.source (old v) (old w))) :
    ∃ next : V ↪ Sigma (SingleStep.successor B phase).Point,
      (∀ v, UnarySource.childLabel (SingleStep.identification B phase)
        (next v).1 = ((old v).1,bits v)) ∧
      (∀ v w, taggedColour B.source
        ((SingleStep.projection B phase).project (next v))
        ((SingleStep.projection B phase).project (next w)) =
        taggedColour B.source (old v) (old w)) ∧
      (∀ (a : Age.Colour B.source) (v w : V),
        originalCurrentExactSaturatedColour A B P base hOne E
          a (old v) (old w) ↔
        originalCurrentExactSaturatedColour A B P base hOne E
          a ((SingleStep.projection B phase).project (next v))
            ((SingleStep.projection B phase).project (next w))) := by
  obtain ⟨next,hOwnerNext,hFine⟩ :=
    originalPhaseFineMarkedChart_nextEmbedding
      B Kroot phase old bits f hOwner hColour
  refine ⟨next,hOwnerNext,hFine,?_⟩
  intro a v w
  exact originalCurrentExactSaturatedColour_taggedColour_iff
    A B P base hOne E a (old v) (old w)
      ((SingleStep.projection B phase).project (next v))
      ((SingleStep.projection B phase).project (next w))
      (hFine v w).symm

end
end CCO.ExactEPGeometry
