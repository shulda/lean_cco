import CCO.FullPhaseLift.Full.Receiving
import CCO.FullPhaseLift.Marked.Signature

/-! Actual irreflexive canonical naming supplies separation, and unary
bits preserve the SAME old guarded names at every later full prefix. -/

universe v
namespace CCO.FullPhaseLift.Full
open Canonical

theorem separatesPoints_expand {L : Signature} {M : Type v} (T : BoolTable L M) :
    SeparatesPoints (expand T) := by
  intro x y h
  have he : twoPoint x y = ![x,y] := by
    funext i
    fin_cases i <;> rfl
  simpa only [he] using expand_separates T x y h

theorem separatesPoints_marked {L : Signature} {M : Type v} {U : BoolTable L M}
    (sep : SeparatesPoints U) (bits : M → APCharacter.Bit) :
    SeparatesPoints (Marked.table U bits) := by
  intro x y h
  obtain ⟨r,slots,ht,hf⟩ := sep x y h
  exact ⟨r.succ,slots,ht,hf⟩

end CCO.FullPhaseLift.Full
