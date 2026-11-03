import CCO.ExactEPGeometry.FullSetoidQuotientLift
import CCO.ExactEPGeometry.OriginalAllCurrentQuotientSource
import CCO.ParityHasse.Original.OrbitalAlgebra

/-!
# B062 C105: ALL invariant equivalences on the actual earlier E quotient

The safe-tower terminality theorem quantifies over the FULL invariant
equivalence lattice, not only RAW-exact kernels. The actual all-parent
simultaneous quotient has the same acting B.G by a proven quotient
action and has actual homogeneous pair orbitals. Consequently ANY
current colour-invariant equivalence containing its true local E
kernel descends to a quotient colour-invariant equivalence. Conversely
ANY quotient colour-invariant equivalence pulls back and is still
colour-invariant upstairs.

This derives both original and quotient colour invariance from their
actual homogeneous group actions. No SAP, full automorphism-group
section, exactness of the tested equivalence or additional hypothesis.
The selected representative/source retyping and final terminality
contradiction are separate C105 steps.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter.Towers
open RigidGroupoid.Geometry
open CCO.ParityHasse.Original

noncomputable section

/-- A genuine arbitrary FULL colour-invariant current equivalence
above the local original E-kernel descends to a whole invariant
equivalence on the REAL all-parent E-quotient source. -/
noncomputable def originalAllCurrentFullInvariantProjection
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    {p : B.Sorts} (F : ColourEq B.source p)
    (hNested : originalExactOnCurrentSort
      A B P transport base hOne E p ≤ F.val) :
    ColourEq
      (originalExactAllCurrentQuotientCurrentSource
        A B P transport base hOne E).source p := by
  let Q : CurrentSource.{u,v,v,t} :=
    originalExactAllCurrentQuotientCurrentSource
      A B P transport base hOne E
  letI : ∀ i : Q.Sorts, MulAction B.G (Q.Point i) := Q.action
  letI : MulAction B.G (Q.Point p) := Q.action p
  let pi : B.Point p → Q.Point p := fun x => Quotient.mk'' x
  have hKernel : ∀ x y, pi x = pi y → F x y := by
    intro x y h
    exact hNested (Quotient.exact h)
  let T : Setoid (Q.Point p) :=
    fullSetoidProjection pi Quotient.mk''_surjective F.val hKernel
  have equivPi : ∀ (g : B.G) (x : B.Point p),
      pi (g • x) = g • pi x := by
    intro g x
    rfl
  have hOld : ∀ (g : B.G) (x y : B.Point p),
      F x y → F (g • x) (g • y) :=
    colourInvariant_groupInvariant B.source B.homogeneous F.2
  have hNew : ∀ (g : B.G) (q r : Q.Point p),
      T q r → T (g • q) (g • r) := by
    intro g q r h
    change CCO.RigidGroupoid.Geometry.Quotient.image pi pi F.val.r q r at h
    change CCO.RigidGroupoid.Geometry.Quotient.image pi pi F.val.r (g • q) (g • r)
    obtain ⟨x,y,hx,hy,hxy⟩ := h
    refine ⟨g • x,g • y,?_,?_,hOld g x y hxy⟩
    · exact (equivPi g x).trans (congrArg (g • ·) hx)
    · exact (equivPi g y).trans (congrArg (g • ·) hy)
  exact ⟨T,groupInvariant_colourInvariant Q.source Q.homogeneous hNew⟩

/-- An arbitrary FULL invariant quotient equivalence pulls back to
an actual current invariant equivalence. It does not need to be
RAW-exact and the current group need not have a section from the
quotient automorphism group. -/
noncomputable def originalAllCurrentFullInvariantPullback
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    {p : B.Sorts}
    (U : ColourEq
      (originalExactAllCurrentQuotientCurrentSource
        A B P transport base hOne E).source p) :
    ColourEq B.source p := by
  let Q : CurrentSource.{u,v,v,t} :=
    originalExactAllCurrentQuotientCurrentSource
      A B P transport base hOne E
  letI : ∀ i : Q.Sorts, MulAction B.G (Q.Point i) := Q.action
  letI : MulAction B.G (Q.Point p) := Q.action p
  let pi : B.Point p → Q.Point p := fun x => Quotient.mk'' x
  let T : Setoid (B.Point p) := Setoid.comap pi U.val
  have equivPi : ∀ (g : B.G) (x : B.Point p),
      pi (g • x) = g • pi x := by
    intro g x
    rfl
  have hNew : ∀ (g : B.G) (x y : Q.Point p),
      U.val.r x y → U.val.r (g • x) (g • y) :=
    colourInvariant_groupInvariant Q.source Q.homogeneous U.2
  have hOld : ∀ (g : B.G) (x y : B.Point p),
      T x y → T (g • x) (g • y) := by
    intro g x y h
    change U.val.r (pi x) (pi y) at h
    change U.val.r (pi (g • x)) (pi (g • y))
    rw [equivPi g x,equivPi g y]
    exact hNew g (pi x) (pi y) h
  exact ⟨T,groupInvariant_colourInvariant B.source B.homogeneous hOld⟩

/-- Every original FULL invariant equivalence containing E is
recovered exactly by inverse image of its invariant quotient.
Crucially, this is a theorem about ALL colour-invariant equivalences
rather than only exact kernels. -/
theorem originalAllCurrentFullInvariant_projection_pullback
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    {p : B.Sorts} (F : ColourEq B.source p)
    (hNested : originalExactOnCurrentSort
      A B P transport base hOne E p ≤ F.val) :
    originalAllCurrentFullInvariantPullback A B P transport base hOne E
      (originalAllCurrentFullInvariantProjection
        A B P transport base hOne E F hNested) = F := by
  apply ColourEq.ext
  intro x y
  let Q : CurrentSource.{u,v,v,t} :=
    originalExactAllCurrentQuotientCurrentSource
      A B P transport base hOne E
  let pi : B.Point p → Q.Point p := fun x => Quotient.mk'' x
  have hKernel : ∀ a b, pi a = pi b → F a b := by
    intro a b h
    exact hNested (Quotient.exact h)
  exact fullSetoidProjection_pullback_iff
    pi Quotient.mk''_surjective F.val hKernel x y

end
end CCO.ExactEPGeometry
