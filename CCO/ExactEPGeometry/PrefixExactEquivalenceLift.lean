import CCO.ExactEPGeometry.CanonicalHistoryExact
import CCO.ExactEPGeometry.OriginalPowers
import CCO.ExactEPGeometry.ExactEquivalenceBasics

/-!
# B062 C31–C33: real exact equivalence lifts across canonical prefixes

Given the ACTUAL two-way exact trace and full (TP) certificates for a
canonical finite character tower, EVERY current nonempty RAW exact
equivalence is the trace of a genuine ORIGINAL RAW exact equivalence.

The proof is the source's real C31–C32 argument:
* forget the current exact presentation to an original nonempty one;
* obtain an ACTUAL original diagonal from a CURRENT reflexive point;
* extend it over the original same sort by original homogeneity;
* stabilize the represented original positive RAW powers;
* use full (TP), with both input traces nonempty, to show every power has
  precisely the original current equivalence trace.

No original or quotient SAP, arbitrary mixed exact descent, quotient
action or stronger assumed preimage is involved. The finite lattice
operations and (E1) homomorphism remain a separately scoped C29–C33 task.
-/

universe u v w t

namespace CCO.ExactEPGeometry.PrefixExactEquivalenceLift

open APCharacter.Towers
open RigidGroupoid.Geometry
open CCO.ExactEPGeometry

noncomputable section

/-- For an arbitrary GIVEN ACTUAL exact/TP transport pair, positive powers
of an original exact D restrict to precisely the same current equivalence.
This is the all-prefix source C32 step, with no independently assumed
stabilization and no finite-index hypothesis. -/
theorem original_power_trace
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (tp : ExactTraceProduct A.source B.source P)
    {p : B.Sorts}
    (D : RawExact.NonemptyExact A.source (P.parent p) (P.parent p))
    (F : B.Point p → B.Point p → Prop)
    (hF : RawSymmetric.EquivRel F)
    (hD : ∀ x y : B.Point p,
      F x y ↔ RawExact.evaluate A.source D.words (P.point p x) (P.point p y))
    (n : ℕ) :
    ∀ x y : B.Point p,
      originalPower (RawExact.evaluate A.source D.words) n
        (P.point p x) (P.point p y) ↔ F x y := by
  induction n with
  | zero =>
      intro x y
      exact (hD x y).symm
  | succ n ih =>
      intro x y
      let R := RawExact.evaluate A.source D.words
      let C := exactCalculus_of_homogeneous_CCO
        A.source A.homogeneous A.cco
      have hFull : FullExact A.source (originalPower R n) :=
        originalPower_exact A.source C R ⟨D,rfl⟩ n
      obtain ⟨Power,hPower⟩ := hFull
      have hInputPower :
          ∃ a b : B.Point p,
            RawExact.evaluate A.source Power.words
              (P.point p a) (P.point p b) := by
        refine ⟨x,x,?_⟩
        rw [hPower]
        exact (ih x x).mpr (hF.refl x)
      have hInputD :
          ∃ a b : B.Point p,
            RawExact.evaluate A.source D.words
              (P.point p a) (P.point p b) :=
        ⟨x,x,(hD x x).mp (hF.refl x)⟩
      have hTP := tp.product Power D hInputPower hInputD x y
      have hStep :
          TRel.comp (RawExact.evaluate A.source Power.words)
            (RawExact.evaluate A.source D.words) =
          originalPower R (n+1) := by
        rw [hPower]
        rfl
      rw [hStep] at hTP
      constructor
      · intro hxy
        obtain ⟨mid,hLeft,hRight⟩ := hTP.mpr hxy
        rw [hPower] at hLeft
        exact hF.trans x mid y ((ih x mid).mp hLeft)
          ((hD mid y).mpr hRight)
      · intro hxy
        apply hTP.mp
        refine ⟨y, ?_, ?_⟩
        · rw [hPower]
          exact (ih x y).mpr hxy
        · exact (hD y y).mp (hF.refl y)

/-- The source C33 SURJECTIVITY component, already for ANY certified
actual finite safe-history prefix: a current exact equivalence lifts to
a FULL original exact equivalence, without altering any current pair
relation on its literal named prefix sort. -/
theorem current_equivalence_has_original_lift
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    {p : B.Sorts}
    (E : RawExact.NonemptyExact B.source p p)
    (hCurrent : RawSymmetric.EquivRel
      (RawExact.evaluate B.source E.words)) :
    ∃ D : RawExact.NonemptyExact A.source (P.parent p) (P.parent p),
      RawSymmetric.EquivRel (RawExact.evaluate A.source D.words) ∧
      ∀ x y : B.Point p,
        RawExact.evaluate B.source E.words x y ↔
          RawExact.evaluate A.source D.words (P.point p x) (P.point p y) := by
  obtain ⟨D,hD⟩ := transport.new_to_old E
  let R := RawExact.evaluate A.source D.words
  have hInv : TRel.Invariant (G := A.G) R :=
    RawExact.presentation_invariant_of_homogeneous A.source
      A.homogeneous D.words
  let a : B.Point p := Classical.choice (B.source.nonemptySort p)
  have hDiag : R (P.point p a) (P.point p a) :=
    (hD a a).mp (hCurrent.refl a)
  have hRef : ∀ x : A.Point (P.parent p), R x x :=
    original_invariant_reflexive_of_one A.source A.homogeneous
      R hInv (P.point p a) hDiag
  let C := exactCalculus_of_homogeneous_CCO
    A.source A.homogeneous A.cco
  have hOldFull : FullExact A.source R := ⟨D,rfl⟩
  obtain ⟨n,hStable⟩ :=
    originalPower_stabilizes A.source A.homogeneous C
      R hOldFull hRef
  obtain ⟨Q,hQ⟩ := originalPower_exact A.source C R hOldFull n
  have hQEquiv : RawSymmetric.EquivRel
      (RawExact.evaluate A.source Q.words) := by
    rw [hQ]
    exact originalPower_equiv_of_stable A.source A.homogeneous C
      R hOldFull hRef n hStable
  refine ⟨Q,hQEquiv,?_⟩
  intro x y
  rw [hQ]
  exact (original_power_trace A B P tp D
    (RawExact.evaluate B.source E.words) hCurrent hD n x y).symm

/-- Actual source instance at ANY chosen canonical prefix: all
original-to-current steps have been discharged by the real AP-only phase,
so no external lift/TP provider remains in the statement. -/
theorem canonical_prefix_equivalence_lift
    {A B : CurrentSource.{u,v,w,t}}
    (h : History CanonicalHistoryExact.CanonicalStep A B)
    {p : B.Sorts}
    (E : RawExact.NonemptyExact B.source p p)
    (hCurrent : RawSymmetric.EquivRel
      (RawExact.evaluate B.source E.words)) :
    let P := CanonicalHistoryExact.historyReduct
      (CanonicalHistoryExact.exactHistory h)
    ∃ D : RawExact.NonemptyExact A.source (P.parent p) (P.parent p),
      RawSymmetric.EquivRel (RawExact.evaluate A.source D.words) ∧
      ∀ x y : B.Point p,
        RawExact.evaluate B.source E.words x y ↔
          RawExact.evaluate A.source D.words (P.point p x) (P.point p y) := by
  dsimp only
  let P := CanonicalHistoryExact.historyReduct
    (CanonicalHistoryExact.exactHistory h)
  exact current_equivalence_has_original_lift A B P
    (CanonicalHistoryExact.canonical_history_transport h)
    (CanonicalHistoryExact.canonical_history_product h) E hCurrent

end
end CCO.ExactEPGeometry.PrefixExactEquivalenceLift
