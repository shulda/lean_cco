import CCO.ResetOrder.Hierarchy.Charts
import Mathlib.Order.WellFounded

/-! Actual coarse-first recursion constructs the orders; preservation and
idempotence are proved rather than supplied as normalization providers. -/
universe u v
namespace CCO.ResetOrder.Hierarchy
structure Schedule (I : Type u) where
  rank : I → ℕ
  count : I → ℕ
  coordinate : ∀ i, Fin (count i) → I
  coordinate_rank : ∀ i a, rank (coordinate i a) < rank i

structure System {I : Type u} (H : Schedule I) (X : I → Type v) where
  parent : ∀ i, X i → X i → Prop
  parent_refl : ∀ i x, parent i x x
  parent_symm : ∀ i {x y}, parent i x y → parent i y x
  parent_trans : ∀ i {x y z}, parent i x y → parent i y z → parent i x z
  up : ∀ i (a : Fin (H.count i)), X i → X (H.coordinate i a)
  key_parent : ∀ i x y, (∀ a, up i a x = up i a y) ↔ parent i x y

namespace System
variable {I : Type u} {H : Schedule I} {X : I → Type v} (S : System H X)
abbrev rank (_S : System H X) := H.rank
abbrev count (_S : System H X) := H.count
abbrev coordinate (_S : System H X) := H.coordinate
abbrev coordinate_rank (_S : System H X) := H.coordinate_rank
abbrev Key (i : I) := (a : Fin (S.count i)) → X (S.coordinate i a)
abbrev key (i : I) (x : X i) : S.Key i := fun a => S.up i a x

theorem key_eq_iff (i : I) (x y : X i) : S.key i x = S.key i y ↔ S.parent i x y := by
  constructor
  · intro h
    exact (S.key_parent i x y).1 (fun a => congrFun h a)
  · intro h
    exact funext ((S.key_parent i x y).2 h)

abbrev Tasks := ∀ i, FibreOrder (S.parent i)
abbrev Orders (_S : System H X) := ∀ i, TotalOrder (X i)
def keyTask (t : S.Tasks) (i : I) : FibreOrder (fun x y => S.key i x = S.key i y) :=
  (t i).changeFibre (fun x y => (S.key_eq_iff i x y).symm)

noncomputable def buildAt (t : S.Tasks) (i : I)
    (earlier : ∀ j, S.rank j < S.rank i → TotalOrder (X j)) : TotalOrder (X i) :=
  fibreLex (S.key i)
    (keyOrder (fun a => earlier (S.coordinate i a) (S.coordinate_rank i a))) (S.keyTask t i)

noncomputable def normalizeTasks (t : S.Tasks) : S.Orders :=
  (measure S.rank).wf.fix (fun i earlier => S.buildAt t i earlier)

theorem normalizeTasks_eq (t : S.Tasks) (i : I) :
    S.normalizeTasks t i = S.buildAt t i (fun j _ => S.normalizeTasks t j) := by
  unfold normalizeTasks
  rw [WellFounded.fix_eq]
  rfl

theorem normalize_lt_iff (t : S.Tasks) (i : I) (x y : X i) :
    (S.normalizeTasks t i).lt x y ↔
      KeyLex (fun a => S.normalizeTasks t (S.coordinate i a)) (S.key i x) (S.key i y) ∨
      (S.parent i x y ∧ (t i).lt x y) := by
  rw [S.normalizeTasks_eq t i]
  change (_ ∨ (S.key i x = S.key i y ∧ (t i).lt x y)) ↔ _
  rw [S.key_eq_iff]
  rfl

theorem normalized_fibre (t : S.Tasks) (i : I) {x y : X i} (hp : S.parent i x y) :
    (S.normalizeTasks t i).lt x y ↔ (t i).lt x y := by
  rw [S.normalizeTasks_eq t i]
  exact fibreLex_same _ _ _ ((S.key_eq_iff i x y).2 hp)

def extract (o : S.Orders) : S.Tasks :=
  fun i => FibreOrder.restrict (o i) (S.parent i) (S.parent_trans i) (S.parent_symm i)

theorem extract_normalize (t : S.Tasks) : S.extract (S.normalizeTasks t) = t := by
  funext i
  apply FibreOrder.ext
  intro x y
  change (S.parent i x y ∧ (S.normalizeTasks t i).lt x y) ↔ (t i).lt x y
  constructor
  · exact fun h => (S.normalized_fibre t i h.1).1 h.2
  · intro h
    exact ⟨(t i).same h, (S.normalized_fibre t i ((t i).same h)).2 h⟩

noncomputable def normalize (o : S.Orders) : S.Orders := S.normalizeTasks (S.extract o)
theorem normalize_idempotent (o : S.Orders) : S.normalize (S.normalize o) = S.normalize o := by
  unfold normalize
  rw [S.extract_normalize]

def ParentLex (o : S.Orders) : Prop :=
  ∀ i x y, (o i).lt x y ↔
    KeyLex (fun a => o (S.coordinate i a)) (S.key i x) (S.key i y) ∨
      (S.parent i x y ∧ (o i).lt x y)

theorem normalize_parentLex (o : S.Orders) : S.ParentLex (S.normalize o) := by
  intro i x y
  change (S.normalizeTasks (S.extract o) i).lt x y ↔ _
  rw [S.normalize_lt_iff]
  apply or_congr Iff.rfl
  apply and_congr_right
  intro hp
  exact (S.normalized_fibre (S.extract o) i hp).symm

theorem parentLex_fixed (o : S.Orders) (ho : S.ParentLex o) : S.normalize o = o := by
  funext i
  induction i using (measure S.rank).wf.induction with
  | h i ih =>
    apply TotalOrder.ext
    intro x y
    change (S.normalizeTasks (S.extract o) i).lt x y ↔ _
    rw [S.normalize_lt_iff, ho i x y]
    apply or_congr
    · unfold KeyLex
      apply exists_congr
      intro a
      have hi : S.normalizeTasks (S.extract o) (S.coordinate i a) = o (S.coordinate i a) :=
        ih (S.coordinate i a) (S.coordinate_rank i a)
      exact and_congr Iff.rfl (Iff.of_eq (congrArg
        (fun q : TotalOrder (X (S.coordinate i a)) => q.lt (S.up i a x) (S.up i a y)) hi))
    · change (S.parent i x y ∧ (S.parent i x y ∧ (o i).lt x y)) ↔ _
      simp only [and_self_left]

theorem parentLex_iff_fixed (o : S.Orders) : S.ParentLex o ↔ S.normalize o = o := by
  constructor
  · exact S.parentLex_fixed o
  · intro h
    rw [← h]
    exact S.normalize_parentLex o
end System
end CCO.ResetOrder.Hierarchy
