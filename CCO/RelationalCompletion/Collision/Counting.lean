import Mathlib.Data.Sym.Card
import Mathlib.Data.Fintype.EquivFin
import Lean.Elab.Tactic.Omega

/-! Pure finite collision counting for B038 C13.  The target type and the
relational alphabet play no role in these counting statements. -/

namespace CCO.RelationalCompletion.Collision

open Finset

universe u v
variable {X : Type u} {Y : Type v} [Fintype X]

noncomputable local instance collisionPropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p
noncomputable local instance collisionTypeDecidableEq (α : Type*) : DecidableEq α :=
  Classical.decEq α

/-- Finite source points selected by a set; no decidability is required of that set. -/
noncomputable def partFinset (T : Set X) : Finset X := univ.filter (fun x => x ∈ T)

@[simp] theorem mem_partFinset (T : Set X) (x : X) : x ∈ partFinset T ↔ x ∈ T := by
  simp [partFinset]

/-- Move precisely the chosen part of one fibre to the new target point. -/
noncomputable def splitMap (h : X → Y) (T : Set X) (fresh : Y) (x : X) : Y :=
  if x ∈ T then fresh else h x

/-- Actual unordered pairs of distinct source points with the same image. -/
noncomputable def collisionPairs (h : X → Y) : Finset (Sym2 X) := by
  classical
  exact ((univ ×ˢ univ).filter (fun p : X × X => p.1 ≠ p.2 ∧ h p.1 = h p.2)).image
    Sym2.mk.uncurry

noncomputable def collisionCount (h : X → Y) : ℕ := (collisionPairs h).card

@[simp] theorem mem_collisionPairs (h : X → Y) (x y : X) :
    s(x, y) ∈ collisionPairs h ↔ x ≠ y ∧ h x = h y := by
  classical
  simp only [collisionPairs, mem_image, mem_filter, mem_product, mem_univ,
    true_and, Prod.exists, Function.uncurry_apply_pair, Sym2.eq_iff]
  constructor
  · rintro ⟨a, b, ⟨hab, he⟩, hxy⟩
    rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hab, he⟩
    · exact ⟨hab.symm, he.symm⟩
  · rintro ⟨hxy, he⟩
    exact ⟨x, y, ⟨hxy, he⟩, Or.inl ⟨rfl, rfl⟩⟩

theorem collisionCount_zero_iff_injective (h : X → Y) :
    collisionCount h = 0 ↔ Function.Injective h := by
  classical
  rw [collisionCount, card_eq_zero, eq_empty_iff_forall_notMem]
  constructor
  · intro hz x y he
    by_contra hn
    exact hz s(x, y) ((mem_collisionPairs h x y).2 ⟨hn, he⟩)
  · intro hinj p
    induction p using Sym2.ind with
    | _ x y => simp only [mem_collisionPairs]; exact fun ⟨hn, he⟩ => hn (hinj he)

/-- The points left in the old fibre after moving `T`. -/
noncomputable def remainder (h : X → Y) (T : Set X) (old : Y) : Finset X := by
  classical
  exact univ.filter (fun x => h x = old ∧ x ∉ T)

@[simp] theorem mem_remainder (h : X → Y) (T : Set X) (old : Y) (x : X) :
    x ∈ remainder h T old ↔ h x = old ∧ x ∉ T := by
  classical
  simp [remainder]

/-- The collisions removed by a split: one endpoint on each side of the cut. -/
noncomputable def crossPairs (h : X → Y) (T : Set X) (old : Y) : Finset (Sym2 X) := by
  classical
  exact ((partFinset T) ×ˢ remainder h T old).image Sym2.mk.uncurry

@[simp] theorem mem_crossPairs (h : X → Y) (T : Set X) (old : Y) (x y : X) :
    s(x, y) ∈ crossPairs h T old ↔
      (x ∈ T ∧ h y = old ∧ y ∉ T) ∨ (y ∈ T ∧ h x = old ∧ x ∉ T) := by
  classical
  simp only [crossPairs, mem_image, mem_product, mem_partFinset, mem_remainder,
    Prod.exists, Function.uncurry_apply_pair, Sym2.eq_iff]
  constructor
  · rintro ⟨a, b, ⟨ha, hb⟩, hh⟩
    rcases hh with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨ha, hb⟩
    · exact Or.inr ⟨ha, hb⟩
  · rintro (⟨hx, hy⟩ | ⟨hy, hx⟩)
    · exact ⟨x, y, ⟨hx, hy⟩, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨y, x, ⟨hy, hx⟩, Or.inr ⟨rfl, rfl⟩⟩

theorem card_crossPairs (h : X → Y) (T : Set X) (old : Y) :
    (crossPairs h T old).card = (partFinset T).card * (remainder h T old).card := by
  classical
  rw [crossPairs, card_image_of_injOn, card_product]
  intro p hp q hq he
  have hp' := mem_product.mp hp
  have hq' := mem_product.mp hq
  rcases Sym2.mk_eq_mk_iff.mp he with he | he
  · exact he
  · have hbad : q.2 ∈ T := by simpa [he] using hp'.1
    exact ((mem_remainder h T old q.2).mp hq'.2).2 hbad |>.elim

theorem collisionPairs_split_union (h : X → Y) (T : Set X) (old fresh : Y)
    (hT : T ⊆ {x | h x = old}) (hfresh : fresh ∉ Set.range h) :
    collisionPairs h = collisionPairs (splitMap h T fresh) ∪ crossPairs h T old := by
  classical
  ext p
  induction p using Sym2.ind with
  | _ x y =>
    simp only [mem_union, mem_collisionPairs, mem_crossPairs]
    have hfx : fresh ≠ h x := fun he => hfresh ⟨x, he.symm⟩
    have hfy : fresh ≠ h y := fun he => hfresh ⟨y, he.symm⟩
    by_cases hx : x ∈ T <;> by_cases hy : y ∈ T
    · simp only [splitMap, hx, hy, ↓reduceIte, and_true,
        not_true_eq_false, and_false, or_false]
      exact ⟨fun hh => hh.1, fun hn => ⟨hn, (hT hx).trans (hT hy).symm⟩⟩
    · simp only [splitMap, hx, hy, ↓reduceIte]
      simp only [true_and, not_false_eq_true, and_true, not_true_eq_false,
        or_false, hfy, and_false, false_or]
      constructor
      · intro hh; exact hh.2.symm.trans (hT hx)
      · intro he; exact ⟨fun heq => hy (heq ▸ hx), (hT hx).trans he.symm⟩
    · simp only [splitMap, hx, hy, ↓reduceIte]
      simp only [false_and, true_and, not_false_eq_true, and_true,
        Ne.symm hfx, and_false, false_or]
      constructor
      · intro hh; exact hh.2.trans (hT hy)
      · intro he; exact ⟨fun heq => hx (heq.symm ▸ hy), he.trans (hT hy).symm⟩
    · simp [splitMap, hx, hy]

theorem collisionPairs_split_disjoint (h : X → Y) (T : Set X) (old fresh : Y)
    (hfresh : fresh ∉ Set.range h) :
    Disjoint (collisionPairs (splitMap h T fresh)) (crossPairs h T old) := by
  classical
  rw [disjoint_left]
  intro p hp hc
  induction p using Sym2.ind with
  | _ x y =>
    have he := ((mem_collisionPairs _ x y).mp hp).2
    rcases (mem_crossPairs h T old x y).mp hc with ⟨hx, _, hy⟩ | ⟨hy, _, hx⟩
    · simp only [splitMap, ite_eq_left hx, ite_eq_right hy] at he
      exact hfresh ⟨y, he.symm⟩
    · simp only [splitMap, ite_eq_right hx, ite_eq_left hy] at he
      exact hfresh ⟨x, he⟩

/-- Exact number of unordered collisions removed; no collision is introduced. -/
theorem collisionCount_split_exact (h : X → Y) (T : Set X) (old fresh : Y)
    (hT : T ⊆ {x | h x = old}) (hfresh : fresh ∉ Set.range h) :
    collisionCount (splitMap h T fresh) + (partFinset T).card * (remainder h T old).card =
      collisionCount h := by
  classical
  unfold collisionCount
  rw [collisionPairs_split_union h T old fresh hT hfresh,
    card_union_of_disjoint (collisionPairs_split_disjoint h T old fresh hfresh),
    card_crossPairs]

theorem collisionCount_split_lt (h : X → Y) (T : Set X) (old fresh : Y)
    (hT : T ⊆ {x | h x = old}) (hfresh : fresh ∉ Set.range h)
    (hleft : T.Nonempty) (hright : ∃ x, h x = old ∧ x ∉ T) :
    collisionCount (splitMap h T fresh) < collisionCount h := by
  classical
  have ht : 0 < (partFinset T).card := card_pos.mpr (by
    obtain ⟨x, hx⟩ := hleft
    exact ⟨x, (mem_partFinset T x).2 hx⟩)
  have hr : 0 < (remainder h T old).card := card_pos.mpr (by
    obtain ⟨x, hx⟩ := hright
    exact ⟨x, (mem_remainder h T old x).2 hx⟩)
  have hpos := Nat.mul_pos ht hr
  have he := collisionCount_split_exact h T old fresh hT hfresh
  omega

/-- The particular proper split used by finite collision unfolding. -/
theorem collisionCount_split_singleton_lt (h : X → Y) (x y : X) (fresh : Y)
    (hxy : x ≠ y) (he : h x = h y) (hfresh : fresh ∉ Set.range h) :
    collisionCount (splitMap h {x} fresh) < collisionCount h := by
  classical
  refine collisionCount_split_lt h {x} (h x) fresh ?_ hfresh ?_ ?_
  · intro z hz
    have hz' : z = x := Set.mem_singleton_iff.mp hz
    simpa [hz']
  · exact ⟨x, Set.mem_singleton x⟩
  · exact ⟨y, he.symm, fun hy => hxy (Set.mem_singleton_iff.mp hy).symm⟩

end CCO.RelationalCompletion.Collision
