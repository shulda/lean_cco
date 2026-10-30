import CCO.UnaryFreshFrames.Examples.MatchingOriginal

/-! The missing-named-factor boundary in the ORIGINAL finite language.
All hypotheses asserted here are constructed; there is no model provider. -/
namespace CCO.UnaryFreshFrames.Examples.Matching
open Structure

theorem original_countable : Countable Point := inferInstance

theorem original_finite_language : Finite originalLanguage.Sorts ∧
    Finite originalLanguage.Func ∧ Finite originalLanguage.Rel :=
  ⟨inferInstance,inferInstance,inferInstance⟩

def projectionTerm : Term originalLanguage 0 1 :=
  Term.func (L := originalLanguage) false (Term.id (L := originalLanguage) 0)

def matchingTerm : Term originalLanguage 0 2 :=
  Term.func (L := originalLanguage) true (Term.id (L := originalLanguage) 0)

theorem projectionTerm_value (q n : ℕ) :
    originalModel.eval projectionTerm (real q n) = rootPoint q := rfl

theorem matchingTerm_value (q n : ℕ) :
    originalModel.eval matchingTerm (real q n) = partner q := rfl

theorem original_term_nonreal {i j : originalLanguage.Sorts} (hi : i ≠ 0)
    (t : Term originalLanguage i j) : i = j ∧ ∀ x, originalModel.eval t x = x := by
  induction t with
  | id => exact ⟨rfl,fun _ => rfl⟩
  | func F t ih => exact False.elim (hi ih.1)

theorem original_no_named_factor : ¬ Nonempty (Term originalLanguage 1 2) := by
  rintro ⟨t⟩
  exact (by decide : (1 : Fin 3) ≠ 2) (original_term_nonreal (by decide) t).1

theorem original_root_closure (q : ℕ) :
    originalModel.closureAt (rootPoint q) = {rootPoint q} := by
  change originalModel.closure {rootPoint q} = _
  rw [original_closure_eq]
  exact root_closure q

theorem original_definable_off_closure (q : ℕ) :
    partner q ∈ Dcl originalModel.Aut {rootPoint q} ∧
      partner q ∉ originalModel.closureAt (rootPoint q) := by
  constructor
  · change partner q ∈ Dcl originalModel.automorphisms {rootPoint q}
    rw [automorphisms_eq]
    exact (definable_off_closure q).1
  · rw [original_root_closure]
    simp [partner,rootPoint]

/-- The existing projection is onto and has a nontrivial actual kernel. -/
theorem projection_onto_noninjective :
    (∀ q, ∃ x : Point, sort x = 0 ∧ operation false x = rootPoint q) ∧
    ∃ x y : Point, sort x = 0 ∧ sort y = 0 ∧ x ≠ y ∧ operation false x = operation false y := by
  refine ⟨fun q => ⟨real q 0,rfl,rfl⟩,?_,?_,?_,?_,?_,?_⟩
  exacts [real 0 0,real 0 1,rfl,rfl,by simp [real],rfl]

theorem forced_on_actual_projection_fibres (x y : Point) (hx : sort x = 0)
    (hy : sort y = 0) (hp : operation false x = operation false y) :
    operation true x = operation true y := by
  obtain ⟨q,n,rfl⟩ := real_of_sort hx
  obtain ⟨r,m,rfl⟩ := real_of_sort hy
  have he : q = r := by simpa [operation,real,rootPoint] using hp
  exact congrArg partner he

/-- The set-theoretic factor is uniquely definable by the one original
matching relation, despite there being NO unary named term for it. -/
theorem unique_matching_partner (q : ℕ) : ∃! s : Point, matchRel (rootPoint q) s := by
  refine ⟨partner q,⟨rfl,rfl,rfl⟩,?_⟩
  intro s hs
  apply point_ext (x := s) (y := partner q) hs.2.1 hs.2.2.symm
  intro h
  exact False.elim ((by decide : (2 : Fin 3) ≠ 0) (hs.2.1.symm.trans h))

theorem original_real_transitive (q n r m : ℕ) :
    ∃ g : originalModel.Aut, g • real q n = real r m := by
  refine ⟨originalAut (wreathAut (Equiv.swap q r) (fun _ => Equiv.swap n m)),?_⟩
  change real ((Equiv.swap q r) q) ((Equiv.swap n m) n) = real r m
  simp

/-- A compact actual witness for the first C49 mechanism. Countability,
finite named signature, homogeneity, local finiteness and real-base orbit
infinitude all hold; the named forced-factor clause still fails. -/
theorem missing_factor_model : originalModel.Homogeneous ∧ originalModel.LocallyFinite ∧
    (∀ D : Set Point, D.Finite → (∀ x ∈ D, sort x = 0) →
      ∀ u, u ∉ originalModel.closure D → (orbitOver originalModel.Aut D u).Infinite) ∧
    ¬ Nonempty (Term originalLanguage 1 2) ∧
    ∀ q, partner q ∈ Dcl originalModel.Aut {rootPoint q} ∧
      partner q ∉ originalModel.closureAt (rootPoint q) :=
  ⟨original_homogeneous,original_locallyFinite,original_real_base_orbits,
    original_no_named_factor,original_definable_off_closure⟩

end CCO.UnaryFreshFrames.Examples.Matching
