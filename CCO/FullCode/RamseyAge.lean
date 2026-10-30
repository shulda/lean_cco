import CCO.FullCode.RamseyCore
import CCO.FullCode.FiniteHidden

/-! Actual finite hidden classes and the embedding Ramsey hypothesis.
Heredity is applied to literal closed induced supports. Ramsey and EP
are separate properties; no root-cover hypothesis enters here. -/
universe u v
namespace CCO.FullCode

def HasHiddenRamsey {L : Language.{u}} (H : FiniteHidden.{u,v} L → Prop) : Prop :=
  ∀ X Y, H X → H Y → ∀ k : ℕ, 0 < k →
    ∃ D, H D ∧ HiddenArrow X.model Y.model D.model k

end CCO.FullCode
