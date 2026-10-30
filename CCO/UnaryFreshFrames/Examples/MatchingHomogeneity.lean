import CCO.UnaryFreshFrames.Examples.Matching
import CCO.UnaryFreshFrames.Examples.FiniteExtension

namespace CCO.UnaryFreshFrames.Examples.Matching
open Structure

def wreath (a : Equiv.Perm ℕ) (b : ℕ → Equiv.Perm ℕ) : Equiv.Perm Point where
  toFun
    | .inl (q,n) => real (a q) (b q n)
    | .inr (.inl q) => rootPoint (a q)
    | .inr (.inr q) => partner (a q)
  invFun
    | .inl (q,n) => real (a.symm q) ((b (a.symm q)).symm n)
    | .inr (.inl q) => rootPoint (a.symm q)
    | .inr (.inr q) => partner (a.symm q)
  left_inv := by
    rintro (⟨q,n⟩ | (q | q))
    all_goals simp [real,rootPoint,partner]
  right_inv := by
    rintro (⟨q,n⟩ | (q | q))
    all_goals simp [real,rootPoint,partner]

theorem wreath_sort (a : Equiv.Perm ℕ) (b : ℕ → Equiv.Perm ℕ) (x : Point) :
    sort (wreath a b x) = sort x := by
  rcases x with ⟨q,n⟩ | (q | q) <;> rfl

theorem wreath_root (a : Equiv.Perm ℕ) (b : ℕ → Equiv.Perm ℕ) (x : Point) :
    root (wreath a b x) = a (root x) := by
  rcases x with ⟨q,n⟩ | (q | q) <;> rfl

theorem wreath_coordinate (a : Equiv.Perm ℕ) (b : ℕ → Equiv.Perm ℕ)
    (x : Point) (hx : sort x = 0) :
    coordinate (wreath a b x) = b (root x) (coordinate x) := by
  rcases x with ⟨q,n⟩ | (q | q)
  · rfl
  · simp [sort] at hx
  · simp [sort] at hx

def wreathAut (a : Equiv.Perm ℕ) (b : ℕ → Equiv.Perm ℕ) : model.Aut := by
  refine ⟨wreath a b, ?_, ?_, ?_⟩
  · exact wreath_sort a b
  · intro F x
    rcases x with ⟨q,n⟩ | (q | q)
    all_goals cases F <;> rfl
  · intro R xs
    change (sort (wreath a b (xs 0)) = R.1 ∧ sort (wreath a b (xs 1)) = R.2 ∧
      root (wreath a b (xs 0)) = root (wreath a b (xs 1))) ↔
      (sort (xs 0) = R.1 ∧ sort (xs 1) = R.2 ∧ root (xs 0) = root (xs 1))
    rw [wreath_sort,wreath_sort,wreath_root,wreath_root]
    simp only [a.injective.eq_iff]

theorem embedding_root_iff (A : model.Piece) (f : A.Embedding Set.univ)
    (x y : A.points) : root (f.point x) = root (f.point y) ↔ root x.val = root y.val := by
  have hsx : sort (f.point x) = sort x.val := f.sort_eq x
  have hsy : sort (f.point y) = sort y.val := f.sort_eq y
  have hr := f.rel_iff (sort x.val,sort y.val) ![x,y]
  change (sort (f.point x) = sort x.val ∧ sort (f.point y) = sort y.val ∧
    root (f.point x) = root (f.point y)) ↔
    (sort x.val = sort x.val ∧ sort y.val = sort y.val ∧ root x.val = root y.val) at hr
  simpa only [hsx,hsy,true_and,eq_self] using hr

/-- Actual finite closed partial isomorphisms extend by a root permutation
and independent fibre permutations. No homogeneity provider is assumed. -/
theorem homogeneous : model.Homogeneous := by
  classical
  intro A f g
  have hroot (x y : A.points) : root (f.point x) = root (f.point y) ↔
      root (g.point x) = root (g.point y) :=
    (embedding_root_iff A f x y).trans (embedding_root_iff A g x y).symm
  obtain ⟨a, ha⟩ := extend_equal_kernels (fun x => root (f.point x))
    (fun x => root (g.point x)) hroot
  let J (q : ℕ) := {x : A.points // sort x.val = 0 ∧ root (f.point x) = q}
  have hb (q : ℕ) : ∃ b : Equiv.Perm ℕ, ∀ x : J q,
      b (coordinate (f.point x.val)) = coordinate (g.point x.val) := by
    apply extend_equal_kernels
    intro x y
    constructor
    · intro hn
      have hsx : sort (f.point x.val) = 0 := (f.sort_eq x.val).trans x.property.1
      have hsy : sort (f.point y.val) = 0 := (f.sort_eq y.val).trans y.property.1
      have he : f.point x.val = f.point y.val := point_ext (hsx.trans hsy.symm)
        (x.property.2.trans y.property.2.symm) (fun _ => hn)
      exact congrArg (fun z => coordinate (g.point z)) (f.injective he)
    · intro hn
      have hsx : sort (g.point x.val) = 0 := (g.sort_eq x.val).trans x.property.1
      have hsy : sort (g.point y.val) = 0 := (g.sort_eq y.val).trans y.property.1
      have hr : root (g.point x.val) = root (g.point y.val) :=
        (ha x.val).symm.trans ((congrArg a (x.property.2.trans y.property.2.symm)).trans (ha y.val))
      have he : g.point x.val = g.point y.val := point_ext (hsx.trans hsy.symm) hr (fun _ => hn)
      exact congrArg (fun z => coordinate (f.point z)) (g.injective he)
  let b : ℕ → Equiv.Perm ℕ := fun q => (hb q).choose
  have hbeta (q : ℕ) (x : J q) : b q (coordinate (f.point x.val)) =
      coordinate (g.point x.val) := (hb q).choose_spec x
  refine ⟨wreathAut a b, ?_⟩
  intro x
  change wreath a b (f.point x) = g.point x
  apply point_ext
  · exact (wreath_sort a b _).trans ((f.sort_eq x).trans (g.sort_eq x).symm)
  · exact (wreath_root a b _).trans (ha x)
  · intro hs
    have hsf : sort (f.point x) = 0 := (wreath_sort a b _).symm.trans hs
    have hsx : sort x.val = 0 := (f.sort_eq x).symm.trans hsf
    rw [wreath_coordinate a b _ hsf]
    exact hbeta (root (f.point x)) ⟨x,hsx,rfl⟩

end CCO.UnaryFreshFrames.Examples.Matching
