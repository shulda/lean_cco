import CCO.ExactEPGeometry.OriginalSelectedQuotientTerminal
import CCO.ExactEPGeometry.CertifiedGateTower
import CCO.ExactEPGeometry.OriginalCodedQuotientSafeHistory
import CCO.ParityHasse.Original.RelativeIndices
import Lean.Elab.Tactic.Omega

/-!
# B062 C104--C105: actual quotient towers and the full terminal implication

The terminal premise in the source concerns covers in the FULL invariant
equivalence lattice, with no RAW exactness restriction. The first equivalence
below identifies that literal premise with the already implemented current
source terminal condition. Finiteness of the actual orbital palette gives a
finite equivalence poset; any proper finite interval contains a cover with a
finite relative class. No extra terminal hypothesis is introduced.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter.Towers CCO.ParityHasse.Original Classical

noncomputable section

/-- The source's terminal condition quantifies over covers in the ENTIRE
colour-invariant equivalence lattice, including non-exact equivalences. -/
def FullInvariantCoverInfinite (B : CurrentSource.{u,v,w,t}) : Prop :=
  ∀ (p : B.Sorts) (E F : ColourEq B.source p), E ⋖ F →
    ∀ a : B.Point p, Infinite (RelativeClass E.val F.val a)

/-- With the actual finite orbital palette, the literal source condition on
FULL invariant covers is equivalent to absence of ANY finite proper interval.
Neither direction restricts either equivalence to the RAW-exact sublattice. -/
theorem terminal_iff_fullInvariantCoverInfinite
    (B : CurrentSource.{u,v,w,t}) :
    B.Terminal ↔ FullInvariantCoverInfinite B := by
  constructor
  · intro ht p E F hEF a
    apply not_finite_iff_infinite.mp
    intro hFinite
    exact ht ⟨p,E,F,a,hEF.lt,hFinite⟩
  · intro hCover
    rintro ⟨p,E,F,a,hEF,hFinite⟩
    obtain ⟨D,hED,hDF⟩ := hEF.exists_covby_le
    letI : Finite (RelativeClass E.val F.val a) := hFinite
    letI : Finite (RelativeClass E.val D.val a) :=
      finite_relative_left E.val D.val F.val hDF a
    letI : Infinite (RelativeClass E.val D.val a) := hCover p E D hED a
    exact not_finite (RelativeClass E.val D.val a)

/-- The actual selected original E-quotient inherits terminality from the
source's precise FULL-cover condition at the final current prefix. The
quotient is the genuine occupancy-selected CurrentSource, rather than an
abstract carrier quotient or an assumed completion. -/
theorem originalExactSelectedQuotient_terminal_of_fullInvariantCovers
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    (hTerminal : FullInvariantCoverInfinite B) :
    (originalExactSelectedQuotientCurrentSource
      A B P transport base hOne E).Terminal :=
  originalExactSelectedQuotient_terminal A B P transport base hOne E
    ((terminal_iff_fullInvariantCoverInfinite B).mpr hTerminal)

/-- The whole quotient-tower source theorem for EVERY specified actual
certified safe history. A quotient edge exists precisely for each original
gate containing E; the other edges are erased by their complete actual source
isomorphisms. Terminality is a separate last implication, with the literal
FULL invariant-cover premise. Each source isomorphism also fixes the literal original saturated quotient
predicate code; its original binary names cannot be renamed. Neither quotient
SAP nor terminality is assumed
to construct the history or to establish its exact retained-stage count. -/
theorem originalExactQuotientSafeTower
    (A : CurrentSource.{u,v,w,t})
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    {s next : CertifiedGateTower.ExactPrefix A}
    (history : History CertifiedGateTower.Step s next) :
    ∃ projected : History CodedSafeSourceStep
        (codedSourceClass (originalCodedQuotient A base hOne E s))
        (codedSourceClass (originalCodedQuotient A base hOne E next)),
      projected.length =
        (certifiedHistoryOriginalGates A base hOne history).countP
          (fun G => decide (E ≤ G)) ∧
      projected.length ≤ history.length ∧
      (FullInvariantCoverInfinite next.current →
        (quotient A base hOne E next).Terminal) := by
  classical
  obtain ⟨projected,hCount⟩ :=
    originalCodedQuotientSafeHistory A base hOne E history
  refine ⟨projected,hCount,?_,?_⟩
  · rw [hCount, ← certifiedHistoryOriginalGates_length A base hOne history]
    exact List.countP_le_length
  · intro hTerminal
    exact originalExactSelectedQuotient_terminal_of_fullInvariantCovers
      A next.current next.reduct next.transport base hOne E hTerminal

/-- There is also a genuine finite terminal example of the whole safe
quotient tower for EVERY original full RAW-exact E, including Id and Top.
Both histories have actual source witnesses, and their lengths are bounded
by the original finite potential. No retained-stage or terminal provider is
requested from the caller: the certified source elimination discharges them.
The zero-stage case is included by the same construction. -/
theorem originalExactQuotientSafeTower_exists
    (A : CurrentSource.{u,v,w,t})
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base) :
    ∃ terminal : CertifiedGateTower.ExactPrefix A,
      ∃ history : History CertifiedGateTower.Step
          (CertifiedGateTower.initial A) terminal,
        terminal.current.Terminal ∧
        history.length + terminal.current.potential ≤ A.potential ∧
        ∃ projected : History CodedSafeSourceStep
            (codedSourceClass
              (originalCodedQuotient A base hOne E (CertifiedGateTower.initial A)))
            (codedSourceClass (originalCodedQuotient A base hOne E terminal)),
          projected.length =
            (certifiedHistoryOriginalGates A base hOne history).countP
              (fun G => decide (E ≤ G)) ∧
          projected.length ≤ A.potential ∧
          (quotient A base hOne E terminal).Terminal := by
  classical
  obtain ⟨terminal,history,hTerminal,hBound,_,_⟩ :=
    CertifiedGateTower.terminalisation A
  obtain ⟨projected,hCount,hLength,hFinal⟩ :=
    originalExactQuotientSafeTower A base hOne E history
  refine ⟨terminal,history,hTerminal,hBound,projected,hCount,?_,?_⟩
  · omega
  · exact hFinal ((terminal_iff_fullInvariantCoverInfinite terminal.current).mp hTerminal)

end
end CCO.ExactEPGeometry
