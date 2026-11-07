import CCO.TerminalHiddenHN.RealExpansion

/-! Expansion property on the literal finite original carriers. The old
host is chosen before EVERY admissible expansion of that same host. -/

universe u v w l k
namespace CCO.TerminalHiddenHN.RealExpansionData
variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}

def EP (E : RealExpansionData.{u,v,w,l,k} S) : Prop :=
  ∀ (A : FiniteInduced (X := X)) (a : E.Expansion A),
    ∃ B : FiniteInduced (X := X),
      ∀ b : E.Expansion B, Nonempty (E.Embedding a b)

end CCO.TerminalHiddenHN.RealExpansionData
