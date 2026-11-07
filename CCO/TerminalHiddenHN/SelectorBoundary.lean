import CCO.UnaryFreshFrames.Language

/-! A selector returning a DIFFERENT real point breaks exact real-root
closure. This is a conditional signature-boundary witness, with no claim
that such a selector belongs to the actual equivariant MI signature. -/

universe u v
namespace CCO.TerminalHiddenHN
open CCO.UnaryFreshFrames
variable {U : Language.{u}} {V : Type v} (P : Structure U V)

/-- A named projection followed by a named return to its real input
sort generates that return value. If the value differs from the starting
point, the real part of its singleton closure has strictly grown. In
particular this applies when the intermediate sort is a proper quotient.
No homogeneity, SAP, CCO or Ramsey hypothesis is involved. -/
theorem selector_violates_real_closure (projection selector : U.Func)
    (hIntermediate : U.output projection = U.input selector)
    (hReturn : U.output selector = U.input projection)
    (x : V) (hx : P.sort x = U.input projection)
    (hDifferent : P.func selector (P.func projection x) ≠ x) :
    P.closure {x} ∩ {y | P.sort y = U.input projection} ≠ {x} := by
  have hProjection : P.func projection x ∈ P.closure {x} :=
    P.closure_closed {x} projection x (P.subset_closure {x} rfl)
  have hSelector : P.func selector (P.func projection x) ∈ P.closure {x} :=
    P.closure_closed {x} selector (P.func projection x) hProjection
  have hReal : P.sort (P.func selector (P.func projection x)) = U.input projection :=
    (P.func_sort selector _ ((P.func_sort projection x hx).trans hIntermediate)).trans hReturn
  intro hExact
  have hSingleton : P.func selector (P.func projection x) ∈ ({x} : Set V) :=
    hExact ▸ (show P.func selector (P.func projection x) ∈
      P.closure {x} ∩ {y | P.sort y = U.input projection} from ⟨hSelector,hReal⟩)
  exact hDifferent (Set.mem_singleton_iff.mp hSingleton)

end CCO.TerminalHiddenHN
