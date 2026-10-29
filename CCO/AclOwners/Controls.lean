import CCO.AclOwners.Rook
import Mathlib.Data.Fin.Basic

/-! A finite diagnostic checks why the rook proof requires TWO
equivalences. This example proves no infinite-source geometry or EPPA. -/
namespace CCO.AclOwners.Controls

def threeRook (i : Fin 3) : Setoid (Fin 3) :=
  Setoid.ker (fun x : Fin 3 => decide (x = i))

theorem three_rook_pairwise_union :
    ∀ x y : Fin 3, ∃ i : Fin 3, threeRook i x y := by
  decide

theorem three_rook_each_fails :
    ∀ i : Fin 3, ∃ x y : Fin 3, ¬ threeRook i x y := by
  decide

theorem three_rook_no_global_class :
    ¬ ∃ i : Fin 3, Concentrated (threeRook i) Set.univ := by
  rintro ⟨i,hi⟩
  obtain ⟨x,y,hxy⟩ := three_rook_each_fails i
  exact hxy (hi x trivial y trivial)

end CCO.AclOwners.Controls
