import Mathlib.GroupTheory.GroupAction.Defs

namespace CCO

/-- CI smoke check only; this is not a theorem exported by the source papers. -/
theorem infrastructure_one_smul {G α : Type*} [Group G] [MulAction G α] (x : α) :
    (1 : G) • x = x := by
  exact one_smul G x

end CCO
