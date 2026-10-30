import CCO.FullPhaseLift.Marked.Class
import CCO.FullPhaseLift.Canonical.Source

/-! The generic full chart construction is instantiated by the ACTUAL
complete canonical names; naming correctness is not an extra source gate. -/
universe v
namespace CCO.FullPhaseLift.Marked
open Canonical
variable {L : Signature} {M : Type v} (U : BoolTable L M)
variable (hsym : SameSortSymmetric U)

theorem actualPairFaithful : PairFaithful U (source U hsym) (Canonical.pack U) := by
  intro V A p q x y
  exact pack_taggedColour_embedding hsym q p x y

end CCO.FullPhaseLift.Marked
