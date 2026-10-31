import CCO.ExactEPGeometry.ExactEquivalenceLattice
import CCO.ExactEPGeometry.PrefixExactEquivalenceLift

/-!
# B062 E1: literal restriction of true finite RAW-exact equivalence lattices

Only a *certified* two-way exact-transport source reduct may be used.
Each original genuine full-RAW-exact equivalence restricts to an actual
current full-RAW-exact equivalence on one REALIZED named sort.

This is not a map on the larger lattice of arbitrary invariant
equivalences, and not an assumption that arbitrary unary refinements or
independent quotients preserve RAW exactness.
-/

universe u v w t

namespace CCO.ExactEPGeometry.PrefixExactRestriction

open APCharacter.Towers
open CCO.ExactEPGeometry
open CCO.ParityHasse.Original
open CCO.RigidGroupoid.Geometry

noncomputable section

variable (A B : CurrentSource.{u,v,w,t})
variable (P : UnaryReduct A.source B.source)
variable (transport : ExactTraceTransport A.source B.source P)
variable (p : B.Sorts)

/-- E1's ACTUAL restriction of an original exact equivalence.
The current exact presentation is CONSTRUCTED using the already proved
old-to-new RAW source transport, with the real diagonal as its required
nonempty trace witness. -/
def rho (E : ExactEq A.source (P.parent p)) : ExactEq B.source p := by
  let R : Setoid (B.Point p) := {
    r := fun x y => E.val (P.point p x) (P.point p y)
    iseqv := {
      refl := by intro x; exact E.val.val.refl (P.point p x)
      symm := by intro x y h; exact E.val.val.symm h
      trans := by intro x y z h k; exact E.val.val.trans h k
    }
  }
  obtain ⟨D,hD⟩ := E.property
  let x : B.Point p := Classical.choice (B.source.nonemptySort p)
  have hReal :
      ∃ a b : B.Point p,
        RawExact.evaluate A.source D.words (P.point p a) (P.point p b) := by
    refine ⟨x,x,?_⟩
    rw [hD]
    exact E.val.val.refl (P.point p x)
  obtain ⟨Q,hQ⟩ := transport.old_to_new D hReal
  have hCurrent : FullExact B.source
      (fun x y : B.Point p => R x y) := by
    refine ⟨Q,?_⟩
    funext a b
    apply propext
    exact (hQ a b).trans (by rw [hD]; exact Iff.rfl)
  have hInvariant : TRel.Invariant (G := B.G)
      (fun x y : B.Point p => R x y) :=
    hCurrent.invariant B.source B.homogeneous
  have hColour : ColourInvariant B.source p R :=
    groupInvariant_colourInvariant B.source B.homogeneous hInvariant
  exact ⟨⟨R,hColour⟩,hCurrent⟩

/-- Restriction means the literal old represented relation evaluated
on the actual projected endpoints, including the diagonal. -/
theorem rho_iff (E : ExactEq A.source (P.parent p))
    (x y : B.Point p) :
    rho A B P transport p E x y ↔
      E (P.point p x) (P.point p y) := Iff.rfl

/-- Restriction is monotone in the ACTUAL inclusion order on the
genuine exact-equivalence sublattice. No unrelated quotient lattice. -/
theorem rho_mono : Monotone (rho A B P transport p) := by
  intro E F hEF
  change (rho A B P transport p E).val ≤
    (rho A B P transport p F).val
  intro x y hxy
  apply (rho_iff A B P transport p F x y).mpr
  exact hEF ((rho_iff A B P transport p E x y).mp hxy)

/-- The actual source-to-current restriction as a monotone order map.
Its join preservation, surjectivity and E2/E3 right adjoint are the
next source obligations, not fields of this definition. -/
def rhoOrder : ExactEq A.source (P.parent p) →o ExactEq B.source p where
  toFun := rho A B P transport p
  monotone' := rho_mono A B P transport p

/-- The original identity exact equivalence remains precisely the
current logical diagonal, not an equality-coloured diversity edge. -/
theorem rho_bot :
    rho A B P transport p (⊥ : ExactEq A.source (P.parent p)) =
      (⊥ : ExactEq B.source p) := by
  apply ExactEq.ext
  intro x y
  exact (rho_iff A B P transport p _ x y).trans
    (show P.point p x = P.point p y ↔ x = y from
      ProjectedWords.point_eq_iff A.source B.source P x y)

/-- Old Top restricts to actual current Top on every inhabited
current sort, including the zero-stage canonical tower. -/
theorem rho_top :
    rho A B P transport p (⊤ : ExactEq A.source (P.parent p)) =
      (⊤ : ExactEq B.source p) := by
  apply ExactEq.ext
  intro x y
  exact (rho_iff A B P transport p _ x y).trans Iff.rfl

/-- C29 meet is literal intersection of real pairs, hence restriction
preserves binary meets of TRUE exact equivalences without an erroneous
support-meet statement for empty atomic intersections. -/
theorem rho_inf
    (E F : ExactEq A.source (P.parent p)) :
    rho A B P transport p (E ⊓ F) =
      rho A B P transport p E ⊓ rho A B P transport p F := by
  apply ExactEq.ext
  intro x y
  change (rho A B P transport p (E ⊓ F)) x y ↔
    ((rho A B P transport p E) x y ∧
      (rho A B P transport p F) x y)
  rw [rho_iff A B P transport p (E ⊓ F) x y,
    rho_iff A B P transport p E x y,
    rho_iff A B P transport p F x y]
  exact Iff.rfl

end
end CCO.ExactEPGeometry.PrefixExactRestriction
