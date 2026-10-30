import CCO.FullPhaseLift.Tower.FiniteAgeReduct
import CCO.FullPhaseLift.Canonical.Expansion

/-! The initial canonical naming is a finite definitional FULL expansion
on the identical carrier. Composing this literal reduct with the actual
finite unary history retains the original pre-naming language as well. -/

universe v
namespace CCO.FullPhaseLift.Full
open Canonical
noncomputable section

/-- Forget exactly the additional canonical names. Every original symbol,
arity, signed tuple and ambient nullary truth has its original meaning. -/
def definitionalReduct {L : Signature} {M : Type v} (T : BoolTable L M) :
    Tower.FullReduct T (expand T) where
  signature := ⟨oldSymbol L,oldSymbol_arity L⟩
  point := Equiv.refl M
  read := by
    funext r xs
    exact expand_old T r xs

end
end CCO.FullPhaseLift.Full
