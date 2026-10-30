import CCO.UnaryFreshFrames.Examples.MatchingHomogeneity

namespace CCO.UnaryFreshFrames.Examples.Matching
open Structure

theorem locallyFinite : model.LocallyFinite := by
  apply model.locallyFinite_of_singletons
  rintro (⟨q,n⟩ | (q | q))
  · change (model.closureAt (real q n)).Finite
    rw [real_closure]
    exact (Set.finite_singleton _).insert _ |>.insert _
  · change (model.closureAt (rootPoint q)).Finite
    rw [root_closure]
    exact Set.finite_singleton _
  · have hc : model.Closed {partner q} := by
      intro F x hx
      have he : x = partner q := hx
      subst x
      rfl
    change (model.closure {partner q}).Finite
    rw [model.closure_eq hc]
    exact Set.finite_singleton _

theorem real_of_sort {x : Point} (hx : sort x = 0) : ∃ q n, x = real q n := by
  rcases x with ⟨q,n⟩ | (q | q)
  · exact ⟨q,n,rfl⟩
  · simp [sort] at hx
  · simp [sort] at hx

def hidden (F : Bool) (q : ℕ) : Point := if F then partner q else rootPoint q

theorem root_hidden (F : Bool) (q : ℕ) : root (hidden F q) = q := by cases F <;> rfl

theorem hidden_orbit_infinite (F : Bool) (q : ℕ) {D : Set Point} (hD : D.Finite)
    (hReal : ∀ x ∈ D, sort x = 0) (hu : hidden F q ∉ model.closure D) :
    (orbitOver model.Aut D (hidden F q)).Infinite := by
  classical
  intro hf
  let Z := D ∪ orbitOver model.Aut D (hidden F q)
  obtain ⟨r, _, hr⟩ := (Set.infinite_univ : (Set.univ : Set ℕ).Infinite).exists_notMem_finite
    ((hD.union hf).image root)
  have hqr (x : Point) (hx : x ∈ D) : root x ≠ q := by
    obtain ⟨p,n,rfl⟩ := real_of_sort (hReal x hx)
    intro he
    change p = q at he
    subst p
    exact hu (model.closure_closed D F (real q n) (model.subset_closure D hx))
  have hrr (x : Point) (hx : x ∈ D) : root x ≠ r := by
    intro he
    exact hr ⟨x,Or.inl hx,he⟩
  let g := wreathAut (Equiv.swap q r) (fun _ => 1)
  have hfix : ∀ x ∈ D, g • x = x := by
    intro x hx
    obtain ⟨p,n,rfl⟩ := real_of_sort (hReal x hx)
    have hpq : p ≠ q := hqr _ hx
    have hpr : p ≠ r := hrr _ hx
    change real ((Equiv.swap q r) p) n = real p n
    rw [Equiv.swap_apply_of_ne_of_ne hpq hpr]
  have hmove : g • hidden F q = hidden F r := by
    cases F <;> simp [hidden,g,wreathAut,wreath,real,rootPoint,partner]
  have hmem : hidden F r ∈ orbitOver model.Aut D (hidden F q) :=
    (mem_orbitOver_iff model.Aut).mpr ⟨g,hfix,hmove⟩
  exact hr ⟨hidden F r,Or.inr hmem,root_hidden F r⟩

theorem real_orbit_infinite (q n : ℕ) {D : Set Point} (hD : D.Finite)
    (hReal : ∀ x ∈ D, sort x = 0) (hu : real q n ∉ model.closure D) :
    (orbitOver model.Aut D (real q n)).Infinite := by
  classical
  intro hf
  obtain ⟨k, _, hk⟩ := (Set.infinite_univ : (Set.univ : Set ℕ).Infinite).exists_notMem_finite
    ((hD.union hf).image coordinate)
  let beta : ℕ → Equiv.Perm ℕ := fun p => if p = q then Equiv.swap n k else 1
  let g := wreathAut 1 beta
  have hfix : ∀ x ∈ D, g • x = x := by
    intro x hx
    obtain ⟨p,m,rfl⟩ := real_of_sort (hReal x hx)
    have hmk : m ≠ k := fun he => hk ⟨real p m,Or.inl hx,he⟩
    by_cases hpq : p = q
    · subst p
      have hmn : m ≠ n := by
        intro he
        subst m
        exact hu (model.subset_closure D hx)
      change real q (beta q m) = real q m
      simp [beta,Equiv.swap_apply_of_ne_of_ne hmn hmk]
    · change real p (beta p m) = real p m
      simp [beta,hpq]
  have hmove : g • real q n = real q k := by
    change real q (beta q n) = real q k
    simp [beta]
  have hmem : real q k ∈ orbitOver model.Aut D (real q n) :=
    (mem_orbitOver_iff model.Aut).mpr ⟨g,hfix,hmove⟩
  exact hk ⟨real q k,Or.inr hmem,rfl⟩

/-- The actual infinite model retains the FULL-automorphism real-base premise
despite its definable off-closure partner over a hidden singleton base. -/
theorem real_base_orbits (D : Set Point) (hD : D.Finite)
    (hReal : ∀ x ∈ D, sort x = 0) (u : Point) (hu : u ∉ model.closure D) :
    (orbitOver model.Aut D u).Infinite := by
  rcases u with ⟨q,n⟩ | (q | q)
  · exact real_orbit_infinite q n hD hReal hu
  · exact hidden_orbit_infinite false q hD hReal hu
  · exact hidden_orbit_infinite true q hD hReal hu

end CCO.UnaryFreshFrames.Examples.Matching
