import CCO.SimultaneousQuotients.Exports
import CCO.SimultaneousQuotients.Towers.Consumers
import CCO.SimultaneousQuotients.Descent.Consumers
import CCO.SimultaneousQuotients.Private.Graph
import CCO.SimultaneousQuotients.Boundaries.PhaseSAP
import CCO.SimultaneousQuotients.Boundaries.MixedProjection
import CCO.SimultaneousQuotients.Boundaries.PhasePresentation

/-! Concrete receiving consumers: the actual infinite homogeneous phase
source, its real two-point exact quotients and top singleton quotients.
The full-group finite-axis theorem is applied to the ACTUAL binary quotient,
while the distinct owner-kernel counterexample retains its proper scope. -/

namespace CCO.SimultaneousQuotients
namespace Consumers
open RawExact Boundaries

abbrev phaseSource := Phase.source Bool
abbrev phaseHomogeneous := Phase.homogeneous Bool
abbrev phaseCycles := Phase.semanticCCO Bool
abbrev phaseK := Phase.phaseKernel Bool
abbrev phaseE := Phase.phaseExact Bool
abbrev phaseRep := Phase.phaseExact_spec Bool

/-- All principal providers close on the genuine infinite source and its
actual finite phase-class carriers. The conclusion uses arbitrary finite
formal vertex universes; it is not a finite-control certificate. -/
theorem phase_quotient_properties :
    SourceProperties phaseSource phaseHomogeneous phaseK phaseE phaseRep :=
  simultaneous_exact_quotients phaseSource phaseHomogeneous phaseK phaseE phaseRep phaseCycles

theorem phaseFinite (i : Bool) : Finite (Carrier phaseK i) :=
  Finite.of_equiv Bool (Phase.phaseQuotientEquiv Bool i).symm

noncomputable abbrev phaseAxes :=
  entireAxes phaseSource phaseHomogeneous phaseK phaseE phaseRep
    (Function.Embedding.refl Bool) phaseFinite

/-- The full Aut(Q) group and the ENTIRE finite quotient axes are used here.
The original infinite clone group and its owner kernel are different objects. -/
theorem actual_full_finite_projection (A : Finset Bool)
    (p : ∀ i : ↥A, phaseAxes.Intrinsic i.val) :
    p ∈ phaseAxes.actualImage A ↔
      ∀ i j : ↥A, i.val ≠ j.val → (p i,p j) ∈ phaseAxes.actualPair i.val j.val :=
  entire_finite_projection phaseSource phaseHomogeneous phaseCycles phaseK phaseE phaseRep
    (Function.Embedding.refl Bool) phaseFinite A p

def topK (i : Bool) : Setoid (Phase.Point Bool i) := ⊤
def topE (i : Bool) : NonemptyExact phaseSource i i := NonemptyExact.top _ i i

theorem topRep (i : Bool) : evaluate phaseSource (topE i).words = (topK i).r :=
  evaluate_nil _

/-- Literal top classes, with an empty restriction list. Even if an actual
quotient diversity edge has full old pullback, it introduces no old paths. -/
theorem top_quotient_properties :
    SourceProperties phaseSource phaseHomogeneous topK topE topRep :=
  simultaneous_exact_quotients phaseSource phaseHomogeneous topK topE topRep phaseCycles

/-- Actual source-to-quotient firewall: ordinary quotient AP/HOM CCO coexists
with a trivial pointwise fine/coarse kernel and a nontrivial intrinsic fibre. -/
theorem actual_owner_kernel_firewall :
    PhaseKernel.descent.ker = ⊥ ∧
    Nat.card (PhaseKernel.fine.induced PhaseKernel.firstAxis).Aut = 2 ∧
    ¬ Nonempty (PhaseKernel.descent.ker ≃*
      (PhaseKernel.fine.induced PhaseKernel.firstAxis).Aut) :=
  ⟨PhaseKernel.pointwise_kernel_trivial,PhaseKernel.actual_intrinsic_card_two,
    PhaseKernel.no_actual_intrinsic_binding⟩

end Consumers
end CCO.SimultaneousQuotients
