import CCO.UnaryFreshFrames.Examples.TwoCoverHomogeneity
import Mathlib.Basic.Countable.Basic

namespace CCO.UnaryFreshFrames.Examples.TwoCover
open Structure

theorem countable_model : Countable Point := inferInstance

theorem locallyFinite : model.LocallyFinite := by
  apply model.locallyFinite_of_singletons
  rintro (⟨⟨q,d⟩,n⟩ | (⟨q,d⟩ | q))
  · change (model.closureAt (real q d n)).Finite
    rw [real_closure]
    exact (Set.finite_singleton _).insert _ |>.insert _ |>.insert _
  · change (model.closureAt (middle q d)).Finite
    rw [middle_closure]
    exact (Set.finite_singleton _).insert _ |>.insert _
  · change (model.closureAt (rootPoint q)).Finite
    rw [root_closure]
    exact Set.finite_singleton _

theorem real_of_sort {x : Point} (hx : sort x = 0) : ∃ q d n, x = real q d n := by
  rcases x with ⟨⟨q,d⟩,n⟩ | (⟨q,d⟩ | q)
  · exact ⟨q,d,n,rfl⟩
  · simp [sort] at hx
  · simp [sort] at hx

def hidden : Option Bool → ℕ → Point
  | none, q => rootPoint q
  | some d, q => middle q d

theorem root_hidden (F : Option Bool) (q : ℕ) : root (hidden F q) = q := by
  cases F <;> rfl

theorem hidden_in_real_closure (F : Option Bool) (q : ℕ) (c : Bool) (n : ℕ) :
    hidden F q ∈ model.closureAt (real q c n) := by
  rw [real_closure]
  cases F with
  | none => exact Or.inr (Or.inr (Or.inr rfl))
  | some d => cases c <;> cases d <;> simp [hidden]

theorem hidden_orbit_infinite (F : Option Bool) (q : ℕ) {D : Set Point} (hD : D.Finite)
    (hReal : ∀ x ∈ D, sort x = 0) (hu : hidden F q ∉ model.closure D) :
    (orbitOver model.Aut D (hidden F q)).Infinite := by
  classical
  intro hf
  obtain ⟨r, _, hr⟩ := (Set.infinite_univ : (Set.univ : Set ℕ).Infinite).exists_notMem_finite
    ((hD.union hf).image root)
  have hqr (x : Point) (hx : x ∈ D) : root x ≠ q := by
    obtain ⟨p,c,n,rfl⟩ := real_of_sort (hReal x hx)
    intro he
    change p = q at he
    subst p
    exact hu (model.closure_mono (Set.singleton_subset_iff.mpr hx)
      (hidden_in_real_closure F q c n))
  have hrr (x : Point) (hx : x ∈ D) : root x ≠ r := by
    intro he
    exact hr ⟨x,Or.inl hx,he⟩
  let g := wreathAut (Equiv.swap q r) (fun _ => 1) (fun _ => 1)
  have hfix : ∀ x ∈ D, g • x = x := by
    intro x hx
    obtain ⟨p,c,n,rfl⟩ := real_of_sort (hReal x hx)
    have hpq : p ≠ q := hqr _ hx
    have hpr : p ≠ r := hrr _ hx
    change real ((Equiv.swap q r) p) c n = real p c n
    rw [Equiv.swap_apply_of_ne_of_ne hpq hpr]
  have hmove : g • hidden F q = hidden F r := by
    cases F <;> simp [hidden,g,wreathAut,wreath,real,middle,rootPoint]
  have hmem : hidden F r ∈ orbitOver model.Aut D (hidden F q) :=
    (mem_orbitOver_iff model.Aut).mpr ⟨g,hfix,hmove⟩
  exact hr ⟨hidden F r,Or.inr hmem,root_hidden F r⟩

theorem real_orbit_infinite (q : ℕ) (d : Bool) (n : ℕ) {D : Set Point} (hD : D.Finite)
    (hReal : ∀ x ∈ D, sort x = 0) (hu : real q d n ∉ model.closure D) :
    (orbitOver model.Aut D (real q d n)).Infinite := by
  classical
  intro hf
  obtain ⟨k, _, hk⟩ := (Set.infinite_univ : (Set.univ : Set ℕ).Infinite).exists_notMem_finite
    ((hD.union hf).image coordinate)
  let beta : (ℕ × Bool) → Equiv.Perm ℕ := fun p => if p = (q,d) then Equiv.swap n k else 1
  let g := wreathAut 1 (fun _ => 1) beta
  have hfix : ∀ x ∈ D, g • x = x := by
    intro x hx
    obtain ⟨p,c,m,rfl⟩ := real_of_sort (hReal x hx)
    have hmk : m ≠ k := fun he => hk ⟨real p c m,Or.inl hx,he⟩
    by_cases hpair : (p,c) = (q,d)
    · have hp : p = q := congrArg Prod.fst hpair
      have hc : c = d := congrArg Prod.snd hpair
      subst p c
      have hmn : m ≠ n := by
        intro he
        subst m
        exact hu (model.subset_closure D hx)
      change real q d (beta (q,d) m) = real q d m
      simp [beta,Equiv.swap_apply_of_ne_of_ne hmn hmk]
    · change real p c (beta (p,c) m) = real p c m
      simp [beta,hpair]
  have hmove : g • real q d n = real q d k := by
    change real q d (beta (q,d) n) = real q d k
    simp [beta]
  have hmem : real q d k ∈ orbitOver model.Aut D (real q d n) :=
    (mem_orbitOver_iff model.Aut).mpr ⟨g,hfix,hmove⟩
  exact hk ⟨real q d k,Or.inr hmem,rfl⟩

/-- Full-Aut off-closure orbits are genuinely infinite over EVERY finite
real base, although the hidden two-cover pair is algebraic over its root. -/
theorem real_base_orbits (D : Set Point) (hD : D.Finite)
    (hReal : ∀ x ∈ D, sort x = 0) (u : Point) (hu : u ∉ model.closure D) :
    (orbitOver model.Aut D u).Infinite := by
  rcases u with ⟨⟨q,d⟩,n⟩ | (⟨q,d⟩ | q)
  · exact real_orbit_infinite q d n hD hReal hu
  · exact hidden_orbit_infinite (some d) q hD hReal hu
  · exact hidden_orbit_infinite none q hD hReal hu

end CCO.UnaryFreshFrames.Examples.TwoCover
