import CCO.RelationalCompletion.Relational.AgeAP
import CCO.RelationalCompletion.Relational.Clone
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Data.Fintype.Option
import Mathlib.Basic.Countable.Basic

/-! C30: one singleton named red sort and infinitely many blue points.
Actual finite induced homogeneity and age AP coexist with failure of SAP
and of injective replacement for the two-red-point source HE. -/
namespace CCO.RelationalCompletion.Relational.BoundariesAP
open Structure

def redLanguage : Language where
  Rel n := PLift (n = 1)

def coloured {V : Type} (red : V → Prop) : Structure redLanguage V where
  rel _ xs := ∀ i, red (xs i)

def target : Structure redLanguage (Option ℕ) := coloured (· = none)

theorem target_countable : Countable (Option ℕ) := inferInstance

theorem embedding_red {V : Type} (B : Structure redLanguage V)
    (f : Embedding B target) (x : V) :
    f.point x = none ↔ B.rel (n := 1) ⟨rfl⟩ (fun _ => x) := by
  have h := f.rel_iff (n := 1) ⟨rfl⟩ (fun _ => x)
  simpa [target, coloured] using h

/-- ACTUAL homogeneity of the countable structure, not a supplied axiom. -/
theorem target_homogeneous : target.Homogeneous := by
  classical
  intro V _ B f g
  let Blue := {x : V // f.point x ≠ none}
  have hblue : ∀ x : Blue, g.point x ≠ none := by
    intro x hg
    exact x.property ((embedding_red B f x).mpr ((embedding_red B g x).mp hg))
  let fp : Option Blue → Option ℕ := fun x => x.elim none (fun y => f.point y)
  let gp : Option Blue → Option ℕ := fun x => x.elim none (fun y => g.point y)
  have hfi : Function.Injective fp := by
    intro x y h
    cases x with
    | none =>
      cases y with
      | none => rfl
      | some y => exact (y.property h.symm).elim
    | some x =>
      cases y with
      | none => exact (x.property h).elim
      | some y => exact congrArg some (Subtype.ext (f.injective h))
  have hgi : Function.Injective gp := by
    intro x y h
    cases x with
    | none =>
      cases y with
      | none => rfl
      | some y => exact (hblue y h.symm).elim
    | some x =>
      cases y with
      | none => exact (hblue x h).elim
      | some y => exact congrArg some (Subtype.ext (g.injective h))
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair fp gp hfi hgi
  have hnone : σ none = none := hσ none
  have hred : ∀ x, σ x = none ↔ x = none := by
    intro x
    constructor
    · intro h
      exact σ.injective (h.trans hnone.symm)
    · rintro rfl
      exact hnone
  let a : Iso target target := {
    point := σ
    rel_iff := by
      intro n R xs
      change (∀ i, σ (xs i) = none) ↔ ∀ i, xs i = none
      exact forall_congr' (fun i => hred (xs i)) }
  refine ⟨a, ?_⟩
  intro x
  by_cases hf : f.point x = none
  · have hg := (embedding_red B g x).mpr ((embedding_red B f x).mp hf)
    change σ (f.point x) = g.point x
    rw [hf, hg]
    exact hnone
  · exact hσ (some ⟨x, hf⟩)

 theorem target_ageAP : target.AgeAP := target_homogeneous.ageAP

/-- Only unary relations occur, so irreducibility forces at most one vertex. -/
theorem unary_irreducible_subsingleton {V : Type} (red : V → Prop)
    (hi : (coloured red).Irreducible) : Subsingleton V := by
  classical
  constructor
  intro x y
  by_contra hne
  let P : Set V := {x}
  let Q : Set V := {z | z ≠ x}
  have hf : (coloured red).FreeSplit P Q := by
    constructor
    · ext z
      simp [P, Q, eq_or_ne]
    · intro n R xs _
      obtain ⟨rfl⟩ := R
      by_cases hx : xs 0 = x
      · left
        intro i
        change xs i = x
        simpa only [Subsingleton.elim i 0] using hx
      · right
        intro i
        change xs i ≠ x
        simpa only [Subsingleton.elim i 0] using hx
  rcases hi P Q hf with hp | hq
  · have hy : y ∈ P := hp ▸ Set.mem_univ y
    exact hne (Set.mem_singleton_iff.mp hy).symm
  · have hx : x ∈ Q := hq ▸ Set.mem_univ x
    exact hx rfl

def twoRed : Structure redLanguage (Fin 2) := coloured (fun _ => True)
def foldRed : Fin 2 → Option ℕ := fun _ => none

theorem foldRed_HE : twoRed.IsHE target foldRed where
  positive _ _ _ _ := rfl
  irreducible S hS := by
    have hs : Subsingleton S := unary_irreducible_subsingleton (fun _ : S => True) hS
    refine ⟨?_, ?_⟩
    · intro x hx y hy _
      exact congrArg Subtype.val (@Subsingleton.elim S hs ⟨x, hx⟩ ⟨y, hy⟩)
    · intro n R xs _
      constructor
      · intro _ i
        trivial
      · intro _ i
        rfl

/-- No positive injection can send two red points to U's sole red point. -/
theorem twoRed_no_injective_hom (h : Fin 2 → Option ℕ)
    (hp : ∀ {n} (R : redLanguage.Rel n) xs,
      twoRed.rel R xs → target.rel R (h ∘ xs)) : ¬Function.Injective h := by
  have h0 : h 0 = none := hp (n := 1) ⟨rfl⟩ (fun _ => 0) (fun _ => trivial) 0
  have h1 : h 1 = none := hp (n := 1) ⟨rfl⟩ (fun _ => 1) (fun _ => trivial) 0
  intro hi
  have he : (0 : Fin 2) = 1 := hi (h0.trans h1.symm)
  exact (by decide : (0 : Fin 2) ≠ 1) he

/-- This ACTUAL countable homogeneous AP-age target does not injectivize HEs. -/
theorem counterexample : target.Homogeneous ∧ target.AgeAP ∧
    twoRed.IsHE target foldRed ∧
    ¬∃ h : Fin 2 → Option ℕ, twoRed.IsHE target h ∧ Function.Injective h := by
  refine ⟨target_homogeneous, target_ageAP, foldRed_HE, ?_⟩
  rintro ⟨h, hh, hi⟩
  exact twoRed_no_injective_hom h hh.positive hi

/-- Strong amalgamation would supply a second red point fresh outside the
entire old singleton, contradicting its explicitly interpreted unary type. -/
theorem target_not_ageSAP : ¬target.AgeSAP := by
  intro hs
  let S : Set (Option ℕ) := {none}
  let : Finite S := (Set.finite_singleton none).to_subtype
  let v : S := ⟨none, Set.mem_singleton none⟩
  obtain ⟨e, _, hfresh⟩ := target.exists_induced_clone target_homogeneous hs S v
  have he : e.point v = none :=
    ((e.rel_iff (n := 1) ⟨rfl⟩ (fun _ => v)).mpr (fun _ => rfl)) 0
  exact hfresh (he.symm ▸ Set.mem_singleton none)

end CCO.RelationalCompletion.Relational.BoundariesAP
