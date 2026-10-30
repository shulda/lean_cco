import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases

namespace CCO.OrbitalCover.Example

def bitBool (b : ZMod 2) : Bool := decide (b = 1)
def boolBit (b : Bool) : ZMod 2 := if b then 1 else 0

@[simp] theorem boolBit_bitBool (b : ZMod 2) : boolBit (bitBool b) = b := by
  fin_cases b <;> rfl

@[simp] theorem bitBool_boolBit (b : Bool) : bitBool (boolBit b) = b := by
  cases b <;> decide

theorem bitBool_injective : Function.Injective bitBool :=
  Function.LeftInverse.injective boolBit_bitBool

@[simp] theorem bitBool_add (a b : ZMod 2) : bitBool (a+b) = (bitBool a ^^ bitBool b) := by
  fin_cases a <;> fin_cases b <;> rfl

@[simp] theorem boolBit_xor (a b : Bool) : boolBit (a ^^ b) = boolBit a + boolBit b := by
  cases a <;> cases b <;> decide

end CCO.OrbitalCover.Example
