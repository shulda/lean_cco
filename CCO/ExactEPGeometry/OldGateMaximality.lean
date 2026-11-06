import CCO.ExactEPGeometry.PrefixExactLargestLift
import CCO.ParityHasse.Relative.Gate

/-!
# B062 C41–C43: pull back a REAL maximal exact complement through E3

This is the precise lattice/geometric part of the old-gate proof.
An original FULL invariant equivalence U covers the ORIGINAL exact
even-walk equivalence Y. The current full U-trace is specified by an
actual pairwise relation equality. A true current maximal RAW-exact
complement to the current Y-trace then lifts, via the already PROVED
right adjoint L_p, to a maximal ORIGINAL full-RAW-exact complement.

Crucial scope: U need NOT be exact, the maximality quantifier includes
ALL actual original RAW-exact equivalences, and no original or quotient
SAP is imposed. The current maximal-gate certificate and the strictness
of the current parity interval are explicit inputs, to be instantiated
by the actual selected source step; they are NOT invented providers.
-/

universe u v w t

namespace CCO.ExactEPGeometry.OldGateMaximality

open APCharacter.Towers
open CCO.ExactEPGeometry
open CCO.ExactEPGeometry.PrefixExactRestriction
open CCO.ExactEPGeometry.PrefixExactLargestLift
open CCO.ParityHasse.Original

noncomputable section

/-- An ACTUAL current gate, maximal among all current RAW-exact
equivalences meeting the full current parity-connected equivalence U
precisely in the exact current even-walk kernel Y. -/
def CurrentGateCandidate
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (p : B.Sorts)
    (Y : ExactEq A.source (P.parent p))
    (U : ColourEq B.source p)
    (K : ExactEq B.source p) : Prop :=
  rho A B P transport p Y ≤ K ∧
    K.val ⊓ U = (rho A B P transport p Y).val

/-- Original exact gate candidates are taken inside the REAL finite
full-RAW-exact equivalence sublattice, while the connectivity upper
equivalence U is in the FULL invariant equivalence lattice. -/
def OriginalGateCandidate
    {ι : Type u} {X : ι → Type v}
    (S : AtomicSource.{u,v,w} ι X) (i : ι)
    (Y : ExactEq S i) (U : ColourEq S i)
    (K : ExactEq S i) : Prop :=
  Y ≤ K ∧ K.val ⊓ U = Y.val

/-- Source C41–C43 order step: for a covered ORIGINAL parity interval,
the L_p lift of the CURRENT maximal exact gate is an ORIGINAL maximal
full-exact complement to that interval. This is not a theorem about
all invariant (potentially nonexact) original equivalences.

The proof uses the actual largest-fiber adjunction, not a chosen
arbitrary predecessor. The two cases for the OLD meet with U come
from the genuinely full invariant Y ⋖ U cover. In the forbidden
case U lies under L_p(K), its real current trace would lie under K,
contradicting strict current parity and the current complement law.
Strictly enlarging the old gate would strictly enlarge the current
exact gate, contradicting current maximality. -/
theorem lift_maximal_gate
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (p : B.Sorts)
    (Y : ExactEq A.source (P.parent p))
    (Uold : ColourEq A.source (P.parent p))
    (Ucur : ColourEq B.source p)
    (hCover : Y.val ⋖ Uold)
    (hUtrace : ∀ x y : B.Point p,
      Ucur x y ↔ Uold (P.point p x) (P.point p y))
    (hStrict : ¬ Ucur ≤ (rho A B P transport p Y).val)
    (K : ExactEq B.source p)
    (hMax : Maximal
      (CurrentGateCandidate A B P transport p Y Ucur) K) :
    Maximal (OriginalGateCandidate A.source (P.parent p) Y Uold)
      (largest A B P transport tp p K) := by
  let L := largest A B P transport tp p K
  have hL := largest_spec A B P transport tp p K
  have hYleL : Y ≤ L := (hL.2 Y).mp hMax.1.1
  have hLower : Y.val ≤ L.val ⊓ Uold :=
    le_inf (show Y.val ≤ L.val from hYleL) hCover.le
  have hMeetCases : L.val ⊓ Uold = Y.val ∨ L.val ⊓ Uold = Uold :=
    hCover.eq_or_eq hLower inf_le_right
  have hMeet : L.val ⊓ Uold = Y.val := by
    rcases hMeetCases with h | h
    · exact h
    · have hUoldLeL : Uold ≤ L.val := by
        rw [← h]
        exact inf_le_left
      have hUcurLeK : Ucur ≤ K.val := by
        intro x y hxy
        have hUold : Uold (P.point p x) (P.point p y) :=
          (hUtrace x y).mp hxy
        have hOldL : L (P.point p x) (P.point p y) :=
          hUoldLeL hUold
        have hCurL : rho A B P transport p L x y :=
          (rho_iff A B P transport p L x y).mpr hOldL
        rw [hL.1] at hCurL
        exact hCurL
      have hUcurLeYcur : Ucur ≤ (rho A B P transport p Y).val := by
        calc
          Ucur ≤ K.val ⊓ Ucur := le_inf hUcurLeK le_rfl
          _ = (rho A B P transport p Y).val := hMax.1.2
      exact (hStrict hUcurLeYcur).elim
  refine ⟨⟨hYleL,hMeet⟩,?_⟩
  intro Z hZ hLZ
  have hYcurLeZcur :
      rho A B P transport p Y ≤ rho A B P transport p Z :=
    rho_mono A B P transport p hZ.1
  have hCurrentMeet :
      (rho A B P transport p Z).val ⊓ Ucur =
        (rho A B P transport p Y).val := by
    apply ColourEq.ext B.source p
    intro x y
    change ((rho A B P transport p Z) x y ∧ Ucur x y) ↔
      (rho A B P transport p Y) x y
    calc
      _ ↔ (Z (P.point p x) (P.point p y) ∧
          Uold (P.point p x) (P.point p y)) :=
        and_congr (rho_iff A B P transport p Z x y) (hUtrace x y)
      _ ↔ Y (P.point p x) (P.point p y) := by
        have hh := congrArg
          (fun V : ColourEq A.source (P.parent p) =>
            V (P.point p x) (P.point p y)) hZ.2
        change (Z (P.point p x) (P.point p y) ∧
          Uold (P.point p x) (P.point p y)) =
          Y (P.point p x) (P.point p y) at hh
        rw [hh]
      _ ↔ (rho A B P transport p Y) x y :=
        (rho_iff A B P transport p Y x y).symm
  have hKleZcur : K ≤ rho A B P transport p Z := by
    calc
      K = rho A B P transport p L := hL.1.symm
      _ ≤ rho A B P transport p Z :=
        rho_mono A B P transport p hLZ
  have hZcurLeK :
      rho A B P transport p Z ≤ K :=
    hMax.2 ⟨hYcurLeZcur,hCurrentMeet⟩ hKleZcur
  exact (hL.2 Z).mp hZcurLeK

end
end CCO.ExactEPGeometry.OldGateMaximality
