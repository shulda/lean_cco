import CCO.ExactEPGeometry.CertifiedGateLabelStep

/-!
# B062 C61: actual finite unary name preservation induction kernel

The exact source's original ONE-sort relation can be tested on
actual projected old global Sigma points. A prefix is label-compatible
with that relation when any two related old projected points have the
SAME ACTUAL current sort name.

At a TRUE AP-only full-character step, the next sort names are
Sigma pairs (current parent, newly assigned REAL child bit). A
previously label-compatible prefix forces equality of their current
parents; actual phase-bit compatibility on pairs of THAT SAME
current parent then forces equality of new child names.

This is a PURE proved composition lemma, not a new source provider:
the phase-bit compatibility premise must actually be discharged by
the previous genuine selected GateChoice source theorem C61.
No invented quotient action, SAP or change of the old relation.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.Towers
open APCharacter.SourceAge
open RigidGroupoid.Geometry

noncomputable section

variable {ι κ : Type u} {X : ι → Type v} {Y : κ → Type v}
variable {S : AtomicSource.{u,v,w} ι X}
variable {T : AtomicSource.{u,v,w} κ Y}

/-- Only the projected actual global old relation, with equality of
current unary sort indices as the conclusion. No false assertion that
the old gate relation is equality on real points. -/
def OriginalRelationRespectsLabels
    (P : UnaryReduct S T) (R : Sigma X → Sigma X → Prop) : Prop :=
  ∀ (a b : Sigma Y),
    R (P.project a) (P.project b) → a.1 = b.1

/-- At the original zero-stage, a genuinely ONE-sort source already
has exactly its unique original unary type. Every old relation
satisfies the label condition (including Top and logical identity). -/
theorem originalRelationRespectsLabels_zero
    (S : AtomicSource.{u,v,w} ι X)
    (hOne : ∀ i j : ι, i = j)
    (R : Sigma X → Sigma X → Prop) :
    OriginalRelationRespectsLabels (UnaryReduct.identity S) R := by
  intro a b _
  exact hOne a.1 b.1

/-- The actual next safe child labels are pairs of the old current
sort and its real valid phase bit. Equality of their full names
follows from the previous source-label property and the genuine
same-parent bit compatibility, with no arbitrary new source sorts.

`hLocal` is exactly the C61 source duty instantiated for the
real GateChoice; this theorem alone does not postulate its truth. -/
theorem originalRelationRespectsLabels_canonical_step
    (B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct S B.source)
    {i : B.Sorts} {K : Kernel B.source i}
    (phase : SourcePhase B.source B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) K)
    (R : Sigma X → Sigma X → Prop)
    (hBefore : OriginalRelationRespectsLabels P R)
    (hLocal : ∀ (j : B.Sorts) (x y : B.Point j),
      R (P.project ⟨j,x⟩) (P.project ⟨j,y⟩) →
        UnarySource.tag (SingleStep.identification B phase) j x =
        UnarySource.tag (SingleStep.identification B phase) j y) :
    OriginalRelationRespectsLabels
      (P.compose (SingleStep.projection B phase)) R := by
  intro ⟨c,x⟩ ⟨d,y⟩ h
  have hCurrent :
      R (P.project ⟨c.1,x.val⟩)
        (P.project ⟨d.1,y.val⟩) := h
  have hParent : c.1 = d.1 :=
    hBefore ⟨c.1,x.val⟩ ⟨d.1,y.val⟩ hCurrent
  rcases c with ⟨j,a⟩
  rcases d with ⟨k,b⟩
  change j = k at hParent
  subst k
  have hTag :
      UnarySource.tag (SingleStep.identification B phase) j x.val =
        UnarySource.tag (SingleStep.identification B phase) j y.val :=
    hLocal j x.val y.val hCurrent
  have hNames : a = b :=
    x.property.symm.trans (hTag.trans y.property)
  exact congrArg (Sigma.mk j) hNames

end
end CCO.ExactEPGeometry
