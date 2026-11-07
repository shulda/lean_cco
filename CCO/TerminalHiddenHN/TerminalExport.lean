import CCO.TerminalHiddenHN.ReadoutTransfer
import CCO.TerminalHiddenHN.ActualInterpretation
import CCO.TerminalHiddenHN.RamseyBridge

/-! Terminal source result. The standalone readout is instantiated on the
ACTUAL terminal hidden interpretation; its sole conditional Ramsey input
is supplied by the proved whole-age HN application on that SAME model.
There is no extra hidden Ramsey, completion, SAP or obstruction provider. -/

universe u v w r
namespace CCO.TerminalHiddenHN
noncomputable section
variable {ι : Type u} {X : ι → Type v} (S : CCO.AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable (H : CCO.HomogeneousSource S G) (sap : CCO.AgeSAP S)
variable (hCover : ∀ i, CCO.TypedOrbitFrames.OriginalAllFullCoversInfinite S (i := i))
variable [∀ i, Countable (X i)]

include H sap hCover

/-- Source `thm:internal-ramsey-terminal`, with FULL original infinite
covers, including Top covers. Every actual hidden/provider duty is
discharged internally; the added finite comparison predicates include
same-root tuples and remember the entire generated hidden order. -/
theorem terminal_finite_relational_ramsey_expansion
    (cco : CCO.SemanticCCO.{u,v,max u v,w} S) :
    HasFiniteRelationalRamseyExpansion.{u,v,w,max u v w,max u v} S := by
  let D := actualInterpretation S H sap hCover
  apply D.hasFiniteRelationalRamseyExpansion_of_hiddenRamsey (HF S H)
  change CCO.FullCode.HasHiddenRamsey (OrderedActualAge S H sap hCover)
  exact actual_hidden_fullcode_ramsey S H sap hCover cco

end
end CCO.TerminalHiddenHN
