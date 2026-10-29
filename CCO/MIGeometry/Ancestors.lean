import Mathlib.Order.UpperLower.CompleteLattice
import Mathlib.Order.Preorder.Finite
import Mathlib.Data.Set.Card

/-! Pure finite-poset minimum ancestors. The index family enumerates ALL
minimal points without repetitions. No source, palette, amalgamation,
exactness or automorphism-group hypothesis occurs in this module. -/

universe u v
namespace CCO.MIGeometry.Ancestors

structure Minima (I : Type v) (P : Type u) [PartialOrder P] where
  point : I → P
  injective : Function.Injective point
  minimal : ∀ i, IsMin (point i)
  complete : ∀ p, IsMin p → ∃ i, point i = p

namespace Minima
variable {I : Type v} {P : Type u} [PartialOrder P] (F : Minima I P)

def ancestors (q : P) : Set I := {i | F.point i ≤ q}

def core (i : I) : LowerSet P :=
  ⟨{q | ¬ F.point i ≤ q}, fun _ _ hab hb ha => hb (ha.trans hab)⟩

def join (i j : I) : LowerSet P := F.core i ⊔ F.core j

def owner (i : I) : LowerSet P := ⨅ j, ⨅ (_ : j ≠ i), F.join i j

def jointOwner : LowerSet P := ⨅ i, ⨅ j, ⨅ (_ : i ≠ j), F.join i j

@[simp] theorem mem_core (i : I) (q : P) :
    q ∈ F.core i ↔ i ∉ F.ancestors q := Iff.rfl

@[simp] theorem mem_join (i j : I) (q : P) :
    q ∈ F.join i j ↔ i ∉ F.ancestors q ∨ j ∉ F.ancestors q := Iff.rfl

theorem ancestors_minimum (i : I) : F.ancestors (F.point i) = {i} := by
  ext j
  change F.point j ≤ F.point i ↔ j = i
  exact ⟨fun h => F.injective ((F.minimal i).eq_of_le h), fun h => h ▸ le_rfl⟩

theorem ancestors_nonempty [Finite P] (q : P) : (F.ancestors q).Nonempty := by
  obtain ⟨p, hpq, hp⟩ := exists_minimal_le_of_wellFoundedLT (fun _ : P => True) q trivial
  have hmin : IsMin p := fun b hb => hp.2 trivial hb
  obtain ⟨i, hi⟩ := F.complete p hmin
  refine ⟨i, ?_⟩
  change F.point i ≤ q
  rwa [hi]

include F in
theorem finite_indices [Finite P] : Finite I := Finite.of_injective F.point F.injective

theorem mem_owner (i : I) (q : P) :
    q ∈ F.owner i ↔ i ∉ F.ancestors q ∨ F.ancestors q = {i} := by
  simp only [owner, LowerSet.mem_iInf_iff, mem_join]
  constructor
  · intro h
    by_cases hi : i ∈ F.ancestors q
    · right
      ext j
      constructor
      · intro hj
        by_contra hji
        exact (h j hji).elim (fun hn => hn hi) (fun hn => hn hj)
      · intro hji
        exact hji ▸ hi
    · exact Or.inl hi
  · rintro (hi | he) j hji
    · exact Or.inl hi
    · right
      rw [he]
      simpa only [Set.mem_singleton_iff] using hji

theorem mem_jointOwner [Finite P] (q : P) :
    q ∈ F.jointOwner ↔ ∃ i, F.ancestors q = {i} := by
  simp only [jointOwner, LowerSet.mem_iInf_iff, mem_join]
  constructor
  · intro h
    obtain ⟨i, hi⟩ := F.ancestors_nonempty q
    refine ⟨i, ?_⟩
    ext j
    constructor
    · intro hj
      by_contra hji
      have hji' : j ≠ i := hji
      exact (h i j hji'.symm).elim (fun hn => hn hi) (fun hn => hn hj)
    · intro hji
      exact hji ▸ hi
  · rintro ⟨k, hk⟩ i j hij
    by_cases hi : i ∈ F.ancestors q
    · right
      intro hj
      have hik : i = k := Set.mem_singleton_iff.mp (hk ▸ hi)
      have hjk : j = k := Set.mem_singleton_iff.mp (hk ▸ hj)
      exact hij (hik.trans hjk.symm)
    · exact Or.inl hi

theorem mem_jointOwner_iff_ncard_one [Finite P] (q : P) :
    q ∈ F.jointOwner ↔ (F.ancestors q).ncard = 1 :=
  (F.mem_jointOwner q).trans Set.ncard_eq_one.symm

theorem core_le_owner (i : I) : F.core i ≤ F.owner i :=
  fun q hq => (F.mem_owner i q).mpr (Or.inl hq)

theorem minimum_mem_owner (i : I) : F.point i ∈ F.owner i :=
  (F.mem_owner i (F.point i)).mpr (Or.inr (F.ancestors_minimum i))

theorem core_lt_owner (i : I) : F.core i < F.owner i := by
  refine lt_of_le_of_ne (F.core_le_owner i) ?_
  intro he
  have h : F.point i ∈ F.core i := he.symm ▸ F.minimum_mem_owner i
  exact h le_rfl

theorem minimum_mem_jointOwner [Finite P] (i : I) : F.point i ∈ F.jointOwner :=
  (F.mem_jointOwner (F.point i)).mpr ⟨i, F.ancestors_minimum i⟩

/-- Even one enumerated minimal point witnesses strictness. The source
application with at least two minima therefore includes this boundary. -/
theorem jointOwner_gt_bot [Finite P] [Nonempty I] :
    (⊥ : LowerSet P) < F.jointOwner := by
  classical
  let i : I := Classical.choice inferInstance
  refine lt_of_le_of_ne bot_le ?_
  intro he
  have h := F.minimum_mem_jointOwner i
  rw [← he] at h
  exact h

theorem inf_owner_eq_jointOwner : (⨅ i, F.owner i) = F.jointOwner := by
  apply SetLike.ext
  intro q
  simp only [owner, jointOwner, LowerSet.mem_iInf_iff]
  exact ⟨fun h i j hij => h i j hij.symm, fun h i j hji => h i j hji.symm⟩

/-- JOG holds for the full owner sets, including the case jointOwner=Top. -/
theorem owner_sup_owner (i j : I) (hij : i ≠ j) :
    F.owner i ⊔ F.owner j = F.join i j := by
  apply SetLike.ext
  intro q
  rw [LowerSet.mem_sup_iff, mem_owner, mem_owner, mem_join]
  constructor
  · rintro ((hi | hi) | (hj | hj))
    · exact Or.inl hi
    · right
      rw [hi]
      simpa only [Set.mem_singleton_iff] using hij.symm
    · exact Or.inr hj
    · left
      rw [hj]
      simpa only [Set.mem_singleton_iff] using hij
  · rintro (hi | hj)
    · exact Or.inl (Or.inl hi)
    · exact Or.inr (Or.inl hj)

end Minima
end CCO.MIGeometry.Ancestors
