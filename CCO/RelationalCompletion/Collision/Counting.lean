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
    simp [hz']
  · exact ⟨x, Set.mem_singleton x⟩
  · exact ⟨y, he.symm, fun hy => hxy (Set.mem_singleton_iff.mp hy).symm⟩

noncomputable def fibreFinset (h : X → Y) (old : Y) : Finset X :=
  univ.filter (fun x => h x = old)

@[simp] theorem mem_fibreFinset (h : X → Y) (old : Y) (x : X) :
    x ∈ fibreFinset h old ↔ h x = old := by
  simp [fibreFinset]

theorem remainder_card (h : X → Y) (T : Set X) (old : Y)
    (hT : T ⊆ {x | h x = old}) :
    (remainder h T old).card = (fibreFinset h old).card - (partFinset T).card := by
  classical
  have hsub : partFinset T ⊆ fibreFinset h old := by
    intro x hx
    exact (mem_fibreFinset h old x).2 (hT ((mem_partFinset T x).mp hx))
  have he : remainder h T old = fibreFinset h old \ partFinset T := by
    ext x
    simp
  rw [he, card_sdiff_of_subset hsub]

/-- C13 in the source notation: `r` is the old fibre size and `t` the moved size. -/
theorem collisionCount_split_exact_sub (h : X → Y) (T : Set X) (old fresh : Y)
    (hT : T ⊆ {x | h x = old}) (hfresh : fresh ∉ Set.range h) :
    collisionCount (splitMap h T fresh) +
      (partFinset T).card * ((fibreFinset h old).card - (partFinset T).card) =
      collisionCount h := by
  simpa only [remainder_card h T old hT] using
    collisionCount_split_exact h T old fresh hT hfresh

/-- The actual finite image; the target itself need not be finite. -/
noncomputable def imageFinset (h : X → Y) : Finset Y := univ.image h

@[simp] theorem mem_imageFinset (h : X → Y) (z : Y) :
    z ∈ imageFinset h ↔ z ∈ Set.range h := by
  simp [imageFinset]

theorem imageFinset_split (h : X → Y) (T : Set X) (old fresh : Y)
    (hT : T ⊆ {x | h x = old})
    (hleft : T.Nonempty) (hright : ∃ x, h x = old ∧ x ∉ T) :
    imageFinset (splitMap h T fresh) = insert fresh (imageFinset h) := by
  classical
  ext z
  simp only [mem_insert, mem_imageFinset, Set.mem_range]
  constructor
  · rintro ⟨x, rfl⟩
    by_cases hx : x ∈ T
    · exact Or.inl (by simp [splitMap, hx])
    · exact Or.inr ⟨x, by simp [splitMap, hx]⟩
  · rintro (rfl | ⟨x, rfl⟩)
    · obtain ⟨x, hx⟩ := hleft
      exact ⟨x, by simp [splitMap, hx]⟩
    · by_cases hx : x ∈ T
      · obtain ⟨y, hy, hyT⟩ := hright
        exact ⟨y, by simpa [splitMap, hyT] using hy.trans (hT hx).symm⟩
      · exact ⟨x, by simp [splitMap, hx]⟩

/-- Equivalently, precisely one new target image is added by a proper split. -/
theorem imageFinset_split_card (h : X → Y) (T : Set X) (old fresh : Y)
    (hT : T ⊆ {x | h x = old}) (hfresh : fresh ∉ Set.range h)
    (hleft : T.Nonempty) (hright : ∃ x, h x = old ∧ x ∉ T) :
    (imageFinset (splitMap h T fresh)).card = (imageFinset h).card + 1 := by
  rw [imageFinset_split h T old fresh hT hleft hright,
    card_insert_of_notMem ((mem_imageFinset h fresh).not.mpr hfresh)]

/-- Unordered collisions contributed by a single actual fibre. -/
noncomputable def fibreCollisionPairs (h : X → Y) (old : Y) : Finset (Sym2 X) :=
  (fibreFinset h old).offDiag.image Sym2.mk.uncurry

theorem card_fibreCollisionPairs (h : X → Y) (old : Y) :
    (fibreCollisionPairs h old).card = ((fibreFinset h old).card).choose 2 := by
  exact Sym2.card_image_offDiag _

theorem fibreFinset_split_fresh (h : X → Y) (T : Set X) (fresh : Y)
    (hfresh : fresh ∉ Set.range h) :
    fibreFinset (splitMap h T fresh) fresh = partFinset T := by
  ext x
  have hn : h x ≠ fresh := fun he => hfresh ⟨x, he⟩
  simp [splitMap, hn]

theorem fibreFinset_split_old (h : X → Y) (T : Set X) (old fresh : Y)
    (hfresh : fresh ∉ Set.range h) (hright : ∃ x, h x = old ∧ x ∉ T) :
    fibreFinset (splitMap h T fresh) old = remainder h T old := by
  obtain ⟨y, hy, _⟩ := hright
  have hne : fresh ≠ old := fun he => hfresh ⟨y, hy.trans he.symm⟩
  ext x
  by_cases hx : x ∈ T <;> simp [splitMap, hx, hne]

theorem fibreFinset_split_other (h : X → Y) (T : Set X) (old fresh z : Y)
    (hT : T ⊆ {x | h x = old}) (hzo : z ≠ old) (hzf : z ≠ fresh) :
    fibreFinset (splitMap h T fresh) z = fibreFinset h z := by
  ext x
  by_cases hx : x ∈ T
  · have he : h x = old := hT hx
    simp [splitMap, hx, he, Ne.symm hzo, Ne.symm hzf]
  · simp [splitMap, hx]

/-- The two replacement fibres have exactly the source's two binomial counts. -/
theorem split_fibre_collision_counts (h : X → Y) (T : Set X) (old fresh : Y)
    (hT : T ⊆ {x | h x = old}) (hfresh : fresh ∉ Set.range h)
    (hright : ∃ x, h x = old ∧ x ∉ T) :
    (fibreCollisionPairs (splitMap h T fresh) fresh).card =
        ((partFinset T).card).choose 2 ∧
      (fibreCollisionPairs (splitMap h T fresh) old).card =
        ((fibreFinset h old).card - (partFinset T).card).choose 2 := by
  rw [card_fibreCollisionPairs, card_fibreCollisionPairs,
    fibreFinset_split_fresh h T fresh hfresh,
    fibreFinset_split_old h T old fresh hfresh hright, remainder_card h T old hT]
  exact ⟨rfl, rfl⟩

end CCO.RelationalCompletion.Collision
