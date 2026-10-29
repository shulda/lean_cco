import CCO.FullRows.RowCompatibility
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Data.ZMod.Basic

/-! Sharp row obstructions, including literal finite binary-group cases. -/
universe u v
namespace CCO.FullRows
variable {I : Type u} {K : Type v} [CommGroup K]

theorem two_rows_cannot_zero (s : Structural I K) (C : Matrix I K)
    (i : I) (f f' : Row I K) (hne : f ≠ f') :
    ¬(rowImage s C i f = 1 ∧ rowImage s C i f' = 1) := by
  rintro ⟨hf,hf'⟩
  exact hne ((rowEquiv s C i).injective (hf.trans hf'.symm))

theorem incompatible_two_requests (hsquare : ∀ g : K, g*g=1)
    (s : Structural I K) (R : I → I → Prop) (C : Matrix I K)
    (i j : I) (hij : i ≠ j) (hr : ¬R i j) (fi fj ri rj : Row I K)
    (hne : ri (s.sigma j) * fi j * s.offset i ≠ rj (s.sigma i) * fj i * s.offset j) :
    ¬(Legal R C ∧ rowImage s C i fi = ri ∧ rowImage s C j fj = rj) := by
  rintro ⟨hC,hi,hj⟩
  have hci := (rowImage_eq_iff_forced hsquare s C i fi ri).mp hi j
  have hcj := (rowImage_eq_iff_forced hsquare s C j fj rj).mp hj i
  exact hne (hci.symm.trans ((hC i j hij hr).trans hcj))

namespace BinaryObstruction
abbrev BitGroup := Multiplicative (ZMod 2)
def bit : BitGroup := Multiplicative.ofAdd (1 : ZMod 2)

theorem bit_ne_one : bit ≠ 1 := by
  change (1 : ZMod 2) ≠ 0
  exact one_ne_zero

theorem square (g : BitGroup) : g*g=1 := by
  change g.toAdd + g.toAdd = 0
  calc
    _ = g.toAdd + (-g.toAdd) := congrArg (g.toAdd + ·) (ZMod.neg_eq_self_mod_two g.toAdd).symm
    _ = 0 := add_neg_cancel _

theorem same_index_obstruction (s : Structural Unit BitGroup) (C : Matrix Unit BitGroup) :
    ¬(rowImage s C () 1 = 1 ∧ rowImage s C () (fun _ => bit) = 1) := by
  apply two_rows_cannot_zero s C () 1 (fun _ => bit)
  intro he
  exact bit_ne_one (congrFun he ()).symm

def identityStructural : Structural Bool BitGroup := ⟨Equiv.refl Bool,fun _ => 1⟩
def firstRow : Row Bool BitGroup := fun j => if j then bit else 1

/-- Two distinct unrecorded indices force unequal opposite matrix entries. -/
theorem unrecorded_pair_obstruction (C : Matrix Bool BitGroup)
    (hC : Legal (fun _ _ : Bool => False) C) :
    ¬(rowImage identityStructural C false firstRow = 1 ∧
      rowImage identityStructural C true 1 = 1) := by
  intro hz
  have hne : (1 : Row Bool BitGroup) (identityStructural.sigma true) * firstRow true *
      identityStructural.offset false ≠
      (1 : Row Bool BitGroup) (identityStructural.sigma false) * (1 : Row Bool BitGroup) false *
      identityStructural.offset true := by
    simpa [identityStructural,firstRow] using bit_ne_one
  exact incompatible_two_requests square identityStructural (fun _ _ : Bool => False)
    C false true Bool.false_ne_true (fun h => h) firstRow 1 1 1 hne ⟨hC,hz⟩

end BinaryObstruction
end CCO.FullRows
