import CCO.FiniteFibres.Boundaries.DifferenceCCO
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Data.Finsupp.Basic
import Mathlib.Tactic.NormNum

/-! C44 and C50 are actual complete difference structures, with their full
automorphism groups and unbounded semantic HOM CCO proved by the common
integration theorem. The infinite example has no finite-palette instance. -/
namespace CCO.FiniteFibres.Boundaries
noncomputable section

namespace DirectedThree
abbrev Point := ZMod 3
abbrev source := Difference.source Point

theorem homogeneous : source.Homogeneous := Difference.homogeneous Point
theorem transitive (x y : Point) : ∃ g : source.Aut, g.val x = y :=
  Difference.transitive Point x y
theorem semanticCCO : Difference.SemanticCCO Point := Difference.semanticCCO Point

theorem fullAut_card : Nat.card source.Aut = 3 := by
  rw [Difference.fullAut_card,Nat.card_eq_fintype_card,ZMod.card]

theorem fullAut_not_power_two : ¬∃ k : ℕ, Nat.card source.Aut = 2^k := by
  rw [fullAut_card]
  rintro ⟨k,hk⟩
  cases k with
  | zero => norm_num at hk
  | succ k =>
      have hd : 2 ∣ 2^(k+1) := ⟨2^k,by rw [pow_succ]; omega⟩
      rw [←hk] at hd
      norm_num at hd

def forward : Difference.Atom Point := ⟨1,by decide⟩

/-- The atom of difference +1 is genuinely directed. Thus no symmetry
premise of the positive two-group and Hasse theorems is satisfied. -/
theorem not_symmetric :
    source.binary forward 0 1 ∧ ¬source.binary forward 1 0 := by
  change ((1 : Point) = 0+1) ∧ ¬((0 : Point) = 1+1)
  decide

end DirectedThree

namespace InfinitePalette

/-- The countable direct sum of copies of the two-element field. -/
abbrev Point := ℕ →₀ ZMod 2
abbrev source := Difference.source Point

instance pointCountable : Countable Point := inferInstance

def basis (n : ℕ) : Point := Finsupp.single n 1

theorem basis_injective : Function.Injective basis := by
  intro m n h
  by_contra hmn
  have hh := congrArg (fun f : Point => f m) h
  simp only [basis,Finsupp.single_eq_same,Finsupp.single_eq_of_ne hmn] at hh
  norm_num at hh

instance pointInfinite : Infinite Point := Infinite.of_injective basis basis_injective

theorem neg_eq_self (x : Point) : -x = x := by
  ext n
  change -(x n) = x n
  have h : ∀ a : ZMod 2, -a = a := by decide
  exact h _

theorem every_atom_symmetric (a : Difference.Atom Point) (x y : Point) :
    source.binary a x y ↔ source.binary a y x := by
  have he : Difference.converse Point a = a := Subtype.ext (neg_eq_self a.val)
  exact (Difference.relation_reverse Point a x y).trans (by rw [he])

theorem homogeneous : source.Homogeneous := Difference.homogeneous Point
theorem transitive (x y : Point) : ∃ g : source.Aut, g.val x = y :=
  Difference.transitive Point x y
theorem semanticCCO : Difference.SemanticCCO Point := Difference.semanticCCO Point

theorem all_real_points_algebraic (a : Point) : Difference.realAcl Point {a} = Set.univ :=
  Difference.realAcl_singleton Point a

theorem singleton_realAcl_infinite (a : Point) :
    (Difference.realAcl Point {a}).Infinite := by
  rw [all_real_points_algebraic]
  exact Set.infinite_univ

theorem every_point_unique_atomic (a x : Point) :
    x = a ∨ ∃ r : Difference.Atom Point, {y | source.binary r a y} = {x} :=
  Difference.unique_atomic_definition Point a x

/-- Every nonzero difference really occurs; there are infinitely many
actual named diversity atoms, rather than merely unused relation names. -/
def basisAtom (n : ℕ) : Difference.Atom Point :=
  ⟨basis n,by
    intro h
    have hh := congrArg (fun f : Point => f n) h
    simp [basis] at hh⟩

theorem basisAtom_injective : Function.Injective basisAtom :=
  fun _ _ h => basis_injective (congrArg Subtype.val h)

instance paletteInfinite : Infinite (Difference.Atom Point) :=
  Infinite.of_injective basisAtom basisAtom_injective

theorem atom_occurs (a : Difference.Atom Point) : source.binary a 0 a.val := by
  change a.val = 0 + a.val
  simp

end InfinitePalette
end
end CCO.FiniteFibres.Boundaries
