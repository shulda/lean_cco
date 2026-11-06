import CCO.ExactEPGeometry.PrefixExactRestrictionSurj

/-!
# B062 E1 / C30: exact-equivalence restriction preserves genuine joins

The source join is the represented product of two ORIGINAL full-exact
equivalences, not an arbitrary invariant relation. The current join
is its genuine finite RAW-exact lattice product. The equality follows
from the C28 nonempty-input (TP) for the entire certified finite
character tower and the actual reflexive diagonal witnesses.

No arbitrary quotient SAP, missing abstract product-homomorphism
premise or selection of an unspecified middle current sort is used.
-/

universe u v w t

namespace CCO.ExactEPGeometry.PrefixExactRestriction

open APCharacter.Towers
open CCO.ExactEPGeometry
open CCO.ParityHasse.Original
open CCO.RigidGroupoid.Geometry

noncomputable section

/-- Source C29/C30: the LITERAL restriction of original exact
equivalence joins is the join of their current exact restrictions.
Both source factors have genuinely nonempty traces, witnessed by
their real diagonals on the FIXED current type p. -/
theorem rho_sup
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (p : B.Sorts)
    (E F : ExactEq A.source (P.parent p)) :
    rho A B P transport p (ExactEq.sup A.homogeneous A.cco E F) =
      ExactEq.sup B.homogeneous B.cco
        (rho A B P transport p E) (rho A B P transport p F) := by
  obtain ⟨D,hD⟩ := E.property
  obtain ⟨K,hK⟩ := F.property
  let a : B.Point p := Classical.choice (B.source.nonemptySort p)
  have hDReal :
      ∃ x y : B.Point p,
        RawExact.evaluate A.source D.words (P.point p x) (P.point p y) := by
    refine ⟨a,a,?_⟩
    simpa only [hD] using E.val.val.refl (P.point p a)
  have hKReal :
      ∃ x y : B.Point p,
        RawExact.evaluate A.source K.words (P.point p x) (P.point p y) := by
    refine ⟨a,a,?_⟩
    simpa only [hK] using F.val.val.refl (P.point p a)
  apply ExactEq.ext
  intro x z
  have hOldJoin :
      (ExactEq.sup A.homogeneous A.cco E F)
        (P.point p x) (P.point p z) ↔
      ∃ m : A.Point (P.parent p),
        E (P.point p x) m ∧ F m (P.point p z) :=
    sup_relation_iff A.source A.homogeneous E.val F.val
      (P.point p x) (P.point p z)
  have hCurrentJoin :
      (ExactEq.sup B.homogeneous B.cco
        (rho A B P transport p E)
        (rho A B P transport p F)) x z ↔
      ∃ m : B.Point p,
        rho A B P transport p E x m ∧
        rho A B P transport p F m z :=
    sup_relation_iff B.source B.homogeneous
      (rho A B P transport p E).val
      (rho A B P transport p F).val x z
  have hTP :
      (∃ m : B.Point p,
        E (P.point p x) (P.point p m) ∧
        F (P.point p m) (P.point p z)) ↔
      (∃ m : A.Point (P.parent p),
        E (P.point p x) m ∧ F m (P.point p z)) := by
    simpa only [hD,hK,TRel.comp] using
      (tp.product D K hDReal hKReal x z)
  calc
    (rho A B P transport p
      (ExactEq.sup A.homogeneous A.cco E F)) x z ↔
        (ExactEq.sup A.homogeneous A.cco E F)
          (P.point p x) (P.point p z) :=
      rho_iff A B P transport p _ x z
    _ ↔ (∃ m : A.Point (P.parent p),
          E (P.point p x) m ∧ F m (P.point p z)) := hOldJoin
    _ ↔ (∃ m : B.Point p,
          E (P.point p x) (P.point p m) ∧
          F (P.point p m) (P.point p z)) := hTP.symm
    _ ↔ (∃ m : B.Point p,
          rho A B P transport p E x m ∧
          rho A B P transport p F m z) := by
      apply exists_congr
      intro m
      exact and_congr
        (rho_iff A B P transport p E x m).symm
        (rho_iff A B P transport p F m z).symm
    _ ↔ (ExactEq.sup B.homogeneous B.cco
          (rho A B P transport p E)
          (rho A B P transport p F)) x z := hCurrentJoin.symm

/-- The source-strength actual full-character history has no
unproved additional premise for preservation of joins. It uses
the same selected history reduct and both already built
source-to-target exactness and (TP) certificates. -/
theorem canonical_prefix_rho_sup
    {A B : CurrentSource.{u,v,w,t}}
    (h : History CanonicalHistoryExact.CanonicalStep A B)
    (p : B.Sorts)
    (E F : ExactEq A.source
      ((CanonicalHistoryExact.historyReduct
        (CanonicalHistoryExact.exactHistory h)).parent p)) :
    let P := CanonicalHistoryExact.historyReduct
      (CanonicalHistoryExact.exactHistory h)
    rho A B P (CanonicalHistoryExact.canonical_history_transport h) p
        (ExactEq.sup A.homogeneous A.cco E F) =
      ExactEq.sup B.homogeneous B.cco
        (rho A B P (CanonicalHistoryExact.canonical_history_transport h) p E)
        (rho A B P (CanonicalHistoryExact.canonical_history_transport h) p F) := by
  dsimp only
  exact rho_sup A B _ (CanonicalHistoryExact.canonical_history_transport h)
    (CanonicalHistoryExact.canonical_history_product h) p E F

end
end CCO.ExactEPGeometry.PrefixExactRestriction
