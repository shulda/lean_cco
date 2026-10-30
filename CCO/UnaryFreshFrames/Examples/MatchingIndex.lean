import CCO.UnaryFreshFrames.Examples.MatchingBoundary
import CCO.UnaryFreshFrames.SAPFresh

namespace CCO.UnaryFreshFrames.Examples.Matching
open Structure

theorem output_real_identity {i j : originalLanguage.Sorts} (t : Term originalLanguage i j) :
    j = 0 → ∀ x, originalModel.eval t x = x := by
  induction t with
  | id => exact fun _ _ => rfl
  | func F t _ =>
    intro hj
    cases F
    · exact False.elim ((by decide : (1 : Fin 3) ≠ 0) hj)
    · exact False.elim ((by decide : (2 : Fin 3) ≠ 0) hj)

/-- These are ALL existing real-source term FUNCTIONS, not merely a selected
finite list of syntax. No named function has a real output sort. -/
theorem real_source_normal_form {j : originalLanguage.Sorts} (t : Term originalLanguage 0 j) :
    (∀ x, originalModel.eval t x = x) ∨
    (∀ x, originalModel.eval t x = operation false x) ∨
    (∀ x, originalModel.eval t x = operation true x) := by
  cases t with
  | id => exact Or.inl (fun _ => rfl)
  | func F t =>
    have ht := output_real_identity t rfl
    cases F
    · exact Or.inr (Or.inl (fun x => congrArg (operation false) (ht x)))
    · exact Or.inr (Or.inr (fun x => congrArg (operation true) (ht x)))

def ForcedActual {j : originalLanguage.Sorts} (t : Term originalLanguage 0 j) : Prop :=
  ∀ x y, sort x = 0 → sort y = 0 → operation false x = operation false y →
    originalModel.eval t x = originalModel.eval t y

def actualFibreValues {j : originalLanguage.Sorts} (t : Term originalLanguage 0 j) (q : ℕ) : Set Point :=
  {y | ∃ x, sort x = 0 ∧ operation false x = rootPoint q ∧ originalModel.eval t x = y}

/-- The first model satisfies the INFINITE-index clause for EVERY unforced
existing term. Its failure is specifically the missing named forced factor. -/
theorem all_unforced_indices_infinite {j : originalLanguage.Sorts}
    (t : Term originalLanguage 0 j) (hn : ¬ ForcedActual t) (q : ℕ) :
    (actualFibreValues t q).Infinite := by
  rcases real_source_normal_form t with hid | hp | ht
  · have hrange : (Set.range (real q)).Infinite :=
      Set.infinite_range_of_injective (by
        intro n m he
        exact congrArg (fun x => coordinate x) he)
    apply hrange.mono
    rintro y ⟨n,rfl⟩
    exact ⟨real q n,rfl,rfl,hid _⟩
  · exact False.elim (hn (fun x y _ _ he => (hp x).trans (he.trans (hp y).symm)))
  · apply False.elim
    apply hn
    intro x y hx hy he
    exact (ht x).trans ((forced_on_actual_projection_fibres x y hx hy he).trans (ht y).symm)

theorem projection_kernels_eq (x y : Point) (hx : sort x = 0) (hy : sort y = 0) :
    operation false x = operation false y ↔ operation true x = operation true y := by
  obtain ⟨q,n,rfl⟩ := real_of_sort hx
  obtain ⟨r,m,rfl⟩ := real_of_sort hy
  simp [operation,real,rootPoint,partner]

def ForcedMatching {j : originalLanguage.Sorts} (t : Term originalLanguage 0 j) : Prop :=
  ∀ x y, sort x = 0 → sort y = 0 → operation true x = operation true y →
    originalModel.eval t x = originalModel.eval t y

theorem forced_matching_iff {j : originalLanguage.Sorts} (t : Term originalLanguage 0 j) :
    ForcedMatching t ↔ ForcedActual t := by
  constructor
  · intro h x y hx hy he
    exact h x y hx hy ((projection_kernels_eq x y hx hy).mp he)
  · intro h x y hx hy he
    exact h x y hx hy ((projection_kernels_eq x y hx hy).mpr he)

def matchingFibreValues {j : originalLanguage.Sorts} (t : Term originalLanguage 0 j) (q : ℕ) : Set Point :=
  {y | ∃ x, sort x = 0 ∧ operation true x = partner q ∧ originalModel.eval t x = y}

theorem matching_fibre_eq {j : originalLanguage.Sorts} (t : Term originalLanguage 0 j) (q : ℕ) :
    matchingFibreValues t q = actualFibreValues t q := by
  ext y
  constructor
  · rintro ⟨x,hx,hp,he⟩
    obtain ⟨r,n,rfl⟩ := real_of_sort hx
    have hr : r = q := by simpa [operation,real,partner] using hp
    subst r
    exact ⟨real q n,rfl,rfl,he⟩
  · rintro ⟨x,hx,hp,he⟩
    obtain ⟨r,n,rfl⟩ := real_of_sort hx
    have hr : r = q := by simpa [operation,real,rootPoint] using hp
    subst r
    exact ⟨real q n,rfl,rfl,he⟩

/-- The other existing named quotient has the same actual fibre equivalence,
so it too satisfies the infinite-index clause for ALL unforced terms. -/
theorem all_unforced_matching_indices_infinite {j : originalLanguage.Sorts}
    (t : Term originalLanguage 0 j) (hn : ¬ ForcedMatching t) (q : ℕ) :
    (matchingFibreValues t q).Infinite := by
  rw [matching_fibre_eq]
  exact all_unforced_indices_infinite t (fun h => hn ((forced_matching_iff t).mpr h)) q

/-- Real-base orbit infinitude does not repair the missing named factor:
this actual homogeneous age fails SAP over a hidden orphan singleton. -/
theorem original_not_ageSAP : ¬ originalModel.AgeSAP := by
  intro hsap
  have hi := originalModel.infiniteClosedOrbits_of_ageSAP original_locallyFinite
    original_homogeneous hsap
  have hc : originalModel.Closed {rootPoint 0} := singleton_root_closed 0
  have hnot : partner 0 ∉ ({rootPoint 0} : Set Point) := by simp [partner,rootPoint]
  exact hi _ (Set.finite_singleton _) hc _ hnot
    ((dcl_subset_acl originalModel.Aut _ ) (original_definable_off_closure 0).1)

end CCO.UnaryFreshFrames.Examples.Matching
