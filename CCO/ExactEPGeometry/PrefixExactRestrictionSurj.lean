import CCO.ExactEPGeometry.PrefixExactRestriction
import CCO.ExactEPGeometry.CanonicalHistoryExact

/-!
# B062 E1: surjectivity of actual exact-equivalence restriction

The C33 original-equivalence envelope proof gives more than a conditional
preimage: for every true current full-RAW-exact equivalence, an ACTUAL
original full-RAW-exact equivalence exists with exactly the same trace.

The source uses only homogeneous real old diagonals and equality-inclusive
positive RAW exact powers, with every TP call retaining nonempty traces.
No quotient SAP or arbitrary source word descent is inserted.
-/

universe u v w t

namespace CCO.ExactEPGeometry.PrefixExactRestriction

open APCharacter.Towers
open CCO.ExactEPGeometry
open CCO.ParityHasse.Original
open CCO.RigidGroupoid.Geometry

noncomputable section

/-- Source C33: the actual restriction map onto the current exact
equivalence lattice is SURJECTIVE. A genuine original equivalence is
constructed, not simply required as a preimage in the hypotheses. -/
theorem rho_surjective
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (p : B.Sorts) :
    Function.Surjective (rho A B P transport p) := by
  intro F
  let Q : RawExact.NonemptyExact B.source p p :=
    Classical.choose F.property
  have hQ : RawExact.evaluate B.source Q.words =
      (fun x y => F.val x y) := Classical.choose_spec F.property
  have hEquiv : RawSymmetric.EquivRel
      (RawExact.evaluate B.source Q.words) := by
    rw [hQ]
    exact ⟨F.val.val.refl,
      fun x y h => F.val.val.symm h,
      fun x y z h k => F.val.val.trans h k⟩
  obtain ⟨D,hDE,hTrace⟩ :=
    PrefixExactEquivalenceLift.current_equivalence_has_original_lift
      A B P transport tp Q hEquiv
  let R : Setoid (A.Point (P.parent p)) := {
    r := RawExact.evaluate A.source D.words
    iseqv := {
      refl := hDE.refl
      symm := by intro x y h; exact hDE.symm x y h
      trans := by intro x y z h k; exact hDE.trans x y z h k
    }
  }
  have hInv : TRel.Invariant (G := A.G)
      (RawExact.evaluate A.source D.words) :=
    RawExact.presentation_invariant_of_homogeneous A.source
      A.homogeneous D.words
  have hColour : ColourInvariant A.source (P.parent p) R :=
    groupInvariant_colourInvariant A.source A.homogeneous hInv
  let Old : ExactEq A.source (P.parent p) :=
    ⟨⟨R,hColour⟩,⟨D,rfl⟩⟩
  refine ⟨Old,?_⟩
  apply ExactEq.ext
  intro x y
  calc
    (rho A B P transport p Old) x y ↔
        Old (P.point p x) (P.point p y) :=
      rho_iff A B P transport p Old x y
    _ ↔ RawExact.evaluate B.source Q.words x y :=
      (hTrace x y).symm
    _ ↔ F x y := by rw [hQ]

/-- The one canonical finite-character tower has no unproved E1
surjectivity parameter: the real stage-by-stage C28 transport and TP
certificates instantiate the full original-exact equivalence lift. -/
theorem canonical_prefix_rho_surjective
    {A B : CurrentSource.{u,v,w,t}}
    (h : History CanonicalHistoryExact.CanonicalStep A B)
    (p : B.Sorts) :
    Function.Surjective (rho A B
      (CanonicalHistoryExact.historyReduct
        (CanonicalHistoryExact.exactHistory h))
      (CanonicalHistoryExact.canonical_history_transport h) p) :=
  rho_surjective A B
    (CanonicalHistoryExact.historyReduct
      (CanonicalHistoryExact.exactHistory h))
    (CanonicalHistoryExact.canonical_history_transport h)
    (CanonicalHistoryExact.canonical_history_product h) p

end
end CCO.ExactEPGeometry.PrefixExactRestriction
