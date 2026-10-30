import CCO.UnaryFreshFrames.Examples.TwoCoverAut

namespace CCO.UnaryFreshFrames.Examples.TwoCover
open Structure

theorem embedding_root_iff (A : model.Piece) (f : A.Embedding Set.univ)
    (x y : A.points) : root (f.point x) = root (f.point y) ↔ root x.val = root y.val := by
  have hsx : sort (f.point x) = sort x.val := f.sort_eq x
  have hsy : sort (f.point y) = sort y.val := f.sort_eq y
  have hr := f.rel_iff (sort x.val,sort y.val) ![x,y]
  change (sort (f.point x) = sort x.val ∧ sort (f.point y) = sort y.val ∧
    root (f.point x) = root (f.point y)) ↔
    (sort x.val = sort x.val ∧ sort y.val = sort y.val ∧ root x.val = root y.val) at hr
  simpa only [hsx,hsy,true_and,eq_self] using hr

/-- Function preservation plus injection reflects the complete τ kernel,
including τ's canonical identity action on the middle sort. -/
theorem embedding_tau_iff (A : model.Piece) (f : A.Embedding Set.univ)
    (x y : A.points) : operation 0 (f.point x) = operation 0 (f.point y) ↔
      operation 0 x.val = operation 0 y.val := by
  constructor
  · intro he
    have h := f.injective ((f.func_eq 0 x).trans (he.trans (f.func_eq 0 y).symm))
    exact congrArg Subtype.val h
  · intro he
    have h : A.func 0 x = A.func 0 y := Subtype.ext he
    exact (f.func_eq 0 x).symm.trans ((congrArg f.point h).trans (f.func_eq 0 y))

theorem tau_eq_iff {x y : Point} (hx : sort x ≠ 2) (hy : sort y ≠ 2) :
    operation 0 x = operation 0 y ↔ root x = root y ∧ bit x = bit y := by
  rcases x with ⟨⟨q,d⟩,n⟩ | (⟨q,d⟩ | q)
  all_goals rcases y with ⟨⟨r,e⟩,m⟩ | (⟨r,e⟩ | r)
  all_goals simp_all [sort,operation,root,bit,middle]

/-- Actual homogeneity on EVERY finite closed induced piece. In particular,
orphan middle fibres contain both swapped points and their root; requests
extend by a root permutation, per-root Bool flips and real-fibre permutations. -/
theorem homogeneous : model.Homogeneous := by
  classical
  intro A f g
  have hroot (x y : A.points) : root (f.point x) = root (f.point y) ↔
      root (g.point x) = root (g.point y) :=
    (embedding_root_iff A f x y).trans (embedding_root_iff A g x y).symm
  obtain ⟨a, ha⟩ := extend_equal_kernels (fun x => root (f.point x))
    (fun x => root (g.point x)) hroot
  let I (q : ℕ) := {x : A.points // sort x.val ≠ 2 ∧ root (f.point x) = q}
  have hc (q : ℕ) : ∃ c : Equiv.Perm Bool, ∀ x : I q,
      c (bit (f.point x.val)) = bit (g.point x.val) := by
    apply extend_equal_kernels
    intro x y
    have hfroot : root (f.point x.val) = root (f.point y.val) := x.property.2.trans y.property.2.symm
    have hgroot : root (g.point x.val) = root (g.point y.val) := (ha x.val).symm.trans
      ((congrArg a hfroot).trans (ha y.val))
    have hfx : sort (f.point x.val) ≠ 2 := fun he => x.property.1 ((f.sort_eq x.val).symm.trans he)
    have hfy : sort (f.point y.val) ≠ 2 := fun he => y.property.1 ((f.sort_eq y.val).symm.trans he)
    have hgx : sort (g.point x.val) ≠ 2 := fun he => x.property.1 ((g.sort_eq x.val).symm.trans he)
    have hgy : sort (g.point y.val) ≠ 2 := fun he => y.property.1 ((g.sort_eq y.val).symm.trans he)
    have he : operation 0 (f.point x.val) = operation 0 (f.point y.val) ↔
        operation 0 (g.point x.val) = operation 0 (g.point y.val) :=
      (embedding_tau_iff A f x.val y.val).trans (embedding_tau_iff A g x.val y.val).symm
    exact (show bit (f.point x.val) = bit (f.point y.val) ↔
        operation 0 (f.point x.val) = operation 0 (f.point y.val) from
      ⟨fun h => (tau_eq_iff hfx hfy).mpr ⟨hfroot,h⟩,
       fun h => ((tau_eq_iff hfx hfy).mp h).2⟩).trans
      (he.trans ⟨fun h => ((tau_eq_iff hgx hgy).mp h).2,
        fun h => (tau_eq_iff hgx hgy).mpr ⟨hgroot,h⟩⟩)
  let c : ℕ → Equiv.Perm Bool := fun q => (hc q).choose
  have hgamma (q : ℕ) (x : I q) : c q (bit (f.point x.val)) = bit (g.point x.val) :=
    (hc q).choose_spec x
  let J (p : ℕ × Bool) := {x : A.points // sort x.val = 0 ∧
    root (f.point x) = p.1 ∧ bit (f.point x) = p.2}
  have hb (p : ℕ × Bool) : ∃ b : Equiv.Perm ℕ, ∀ x : J p,
      b (coordinate (f.point x.val)) = coordinate (g.point x.val) := by
    apply extend_equal_kernels
    intro x y
    have hsx : sort x.val.val ≠ 2 := by rw [x.property.1]; decide
    have hsy : sort y.val.val ≠ 2 := by rw [y.property.1]; decide
    have hfx : sort (f.point x.val) = 0 := (f.sort_eq x.val).trans x.property.1
    have hfy : sort (f.point y.val) = 0 := (f.sort_eq y.val).trans y.property.1
    have hgx : sort (g.point x.val) = 0 := (g.sort_eq x.val).trans x.property.1
    have hgy : sort (g.point y.val) = 0 := (g.sort_eq y.val).trans y.property.1
    have hfr : root (f.point x.val) = root (f.point y.val) := x.property.2.1.trans y.property.2.1.symm
    have hfb : bit (f.point x.val) = bit (f.point y.val) := x.property.2.2.trans y.property.2.2.symm
    have hgr : root (g.point x.val) = root (g.point y.val) := (ha x.val).symm.trans
      ((congrArg a hfr).trans (ha y.val))
    have hgb : bit (g.point x.val) = bit (g.point y.val) :=
      (hgamma p.1 ⟨x.val,hsx,x.property.2.1⟩).symm.trans
        ((congrArg (c p.1) hfb).trans (hgamma p.1 ⟨y.val,hsy,y.property.2.1⟩))
    constructor
    · intro hn
      have he := point_ext (hfx.trans hfy.symm) hfr (fun _ => hfb) (fun _ => hn)
      exact congrArg (fun z => coordinate (g.point z)) (f.injective he)
    · intro hn
      have he := point_ext (hgx.trans hgy.symm) hgr (fun _ => hgb) (fun _ => hn)
      exact congrArg (fun z => coordinate (f.point z)) (g.injective he)
  let b : (ℕ × Bool) → Equiv.Perm ℕ := fun p => (hb p).choose
  have hbeta (p : ℕ × Bool) (x : J p) : b p (coordinate (f.point x.val)) =
      coordinate (g.point x.val) := (hb p).choose_spec x
  refine ⟨wreathAut a c b, ?_⟩
  intro x
  change wreath a c b (f.point x) = g.point x
  apply point_ext
  · exact (wreath_sort a c b _).trans ((f.sort_eq x).trans (g.sort_eq x).symm)
  · exact (wreath_root a c b _).trans (ha x)
  · intro hs
    have hsf : sort (f.point x) ≠ 2 := fun he => hs ((wreath_sort a c b _).trans he)
    have hsx : sort x.val ≠ 2 := fun he => hsf ((f.sort_eq x).trans he)
    rw [wreath_bit a c b _ hsf]
    exact hgamma (root (f.point x)) ⟨x,hsx,rfl⟩
  · intro hs
    have hsf : sort (f.point x) = 0 := (wreath_sort a c b _).symm.trans hs
    have hsx : sort x.val = 0 := (f.sort_eq x).symm.trans hsf
    rw [wreath_coordinate a c b _ hsf]
    exact hbeta (root (f.point x),bit (f.point x)) ⟨x,hsx,rfl,rfl⟩

end CCO.UnaryFreshFrames.Examples.TwoCover
