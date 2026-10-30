import CCO.UnaryFreshFrames.Examples.TwoCover
import CCO.UnaryFreshFrames.Examples.FiniteExtension

/-! Concrete full automorphisms: arbitrary root permutations, independent
per-root Bool flips and independent permutations of each infinite real fibre. -/
namespace CCO.UnaryFreshFrames.Examples.TwoCover
open Structure

theorem bool_perm_not (e : Equiv.Perm Bool) (b : Bool) : e (!b) = !(e b) := by
  have hne : e (!b) ≠ e b := by
    intro he
    have hh := e.injective he
    cases b <;> cases hh
  cases hb : e b <;> cases hn : e (!b) <;> simp_all

def wreath (a : Equiv.Perm ℕ) (c : ℕ → Equiv.Perm Bool)
    (b : (ℕ × Bool) → Equiv.Perm ℕ) : Equiv.Perm Point where
  toFun
    | .inl ((q,d),n) => real (a q) (c q d) (b (q,d) n)
    | .inr (.inl (q,d)) => middle (a q) (c q d)
    | .inr (.inr q) => rootPoint (a q)
  invFun
    | .inl ((q,d),n) => real (a.symm q) ((c (a.symm q)).symm d)
        ((b (a.symm q,(c (a.symm q)).symm d)).symm n)
    | .inr (.inl (q,d)) => middle (a.symm q) ((c (a.symm q)).symm d)
    | .inr (.inr q) => rootPoint (a.symm q)
  left_inv := by
    rintro (⟨⟨q,d⟩,n⟩ | (⟨q,d⟩ | q))
    all_goals simp [real,middle,rootPoint]
  right_inv := by
    rintro (⟨⟨q,d⟩,n⟩ | (⟨q,d⟩ | q))
    all_goals simp [real,middle,rootPoint]

theorem wreath_sort (a : Equiv.Perm ℕ) (c : ℕ → Equiv.Perm Bool)
    (b : (ℕ × Bool) → Equiv.Perm ℕ) (x : Point) :
    sort (wreath a c b x) = sort x := by
  rcases x with ⟨⟨q,d⟩,n⟩ | (⟨q,d⟩ | q) <;> rfl

theorem wreath_root (a : Equiv.Perm ℕ) (c : ℕ → Equiv.Perm Bool)
    (b : (ℕ × Bool) → Equiv.Perm ℕ) (x : Point) :
    root (wreath a c b x) = a (root x) := by
  rcases x with ⟨⟨q,d⟩,n⟩ | (⟨q,d⟩ | q) <;> rfl

theorem wreath_bit (a : Equiv.Perm ℕ) (c : ℕ → Equiv.Perm Bool)
    (b : (ℕ × Bool) → Equiv.Perm ℕ) (x : Point) (hx : sort x ≠ 2) :
    bit (wreath a c b x) = c (root x) (bit x) := by
  rcases x with ⟨⟨q,d⟩,n⟩ | (⟨q,d⟩ | q)
  · rfl
  · rfl
  · exact False.elim (hx rfl)

theorem wreath_coordinate (a : Equiv.Perm ℕ) (c : ℕ → Equiv.Perm Bool)
    (b : (ℕ × Bool) → Equiv.Perm ℕ) (x : Point) (hx : sort x = 0) :
    coordinate (wreath a c b x) = b (root x,bit x) (coordinate x) := by
  rcases x with ⟨⟨q,d⟩,n⟩ | (⟨q,d⟩ | q)
  · rfl
  · simp [sort] at hx
  · simp [sort] at hx

def wreathAut (a : Equiv.Perm ℕ) (c : ℕ → Equiv.Perm Bool)
    (b : (ℕ × Bool) → Equiv.Perm ℕ) : model.Aut := by
  refine ⟨wreath a c b, wreath_sort a c b, ?_, ?_⟩
  · intro F x
    rcases x with ⟨⟨q,d⟩,n⟩ | (⟨q,d⟩ | q)
    all_goals fin_cases F
    all_goals try rfl
    change middle (a q) (c q (!d)) = middle (a q) (!(c q d))
    rw [bool_perm_not]
  · intro R xs
    change (sort (wreath a c b (xs 0)) = R.1 ∧ sort (wreath a c b (xs 1)) = R.2 ∧
      root (wreath a c b (xs 0)) = root (wreath a c b (xs 1))) ↔
      (sort (xs 0) = R.1 ∧ sort (xs 1) = R.2 ∧ root (xs 0) = root (xs 1))
    rw [wreath_sort,wreath_sort,wreath_root,wreath_root]
    simp only [a.injective.eq_iff]

/-- Every actual original real sort point moves to every other one. -/
theorem real_transitive (q r : ℕ) (d e : Bool) (n m : ℕ) :
    ∃ g : model.Aut, g • real q d n = real r e m := by
  refine ⟨wreathAut (Equiv.swap q r) (fun _ => Equiv.swap d e)
    (fun _ => Equiv.swap n m), ?_⟩
  change real (Equiv.swap q r q) (Equiv.swap d e d) (Equiv.swap n m n) = _
  simp

end CCO.UnaryFreshFrames.Examples.TwoCover
