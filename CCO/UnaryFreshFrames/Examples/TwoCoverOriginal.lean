import CCO.UnaryFreshFrames.Examples.TwoCoverKernels

/-! The second model in the ORIGINAL relationally empty language. The
auxiliary typed root-equality predicates are already equalities of named
p/r/id values on closed pieces; hence they do not strengthen homogeneity,
change the full group, or introduce a named factor term. -/
namespace CCO.UnaryFreshFrames.Examples.TwoCover
open Structure

abbrev originalLanguage : Language where
  Sorts := Fin 3
  Func := Fin 4
  Rel := Empty
  input := language.input
  output := language.output
  arity R := nomatch R
  argument R := nomatch R

abbrev originalModel : Structure originalLanguage Point where
  sort := sort
  func := operation
  func_sort := model.func_sort
  func_offsort := model.func_offsort
  rel R := nomatch R
  rel_sort R := nomatch R

/-- On each source sort the root is an ACTUAL named p, r, or identity term. -/
def rootValue (x : Point) : Point :=
  if sort x = 0 then operation 2 x else if sort x = 1 then operation 1 x else x

theorem rootValue_eq (x : Point) : rootValue x = rootPoint (root x) := by
  rcases x with ⟨⟨q,d⟩,n⟩ | (⟨q,d⟩ | q) <;> rfl

theorem root_eq_iff_values (x y : Point) : root x = root y ↔ rootValue x = rootValue y := by
  rw [rootValue_eq,rootValue_eq]
  constructor
  · exact congrArg rootPoint
  · intro h
    have he := congrArg root h
    exact he

theorem rootValue_closed (A : originalModel.Piece) (x : A.points) :
    rootValue x.val ∈ A.points := by
  unfold rootValue
  split_ifs
  · exact A.closed 2 x.val x.property
  · exact A.closed 1 x.val x.property
  · exact x.property

abbrev expandedPiece (A : originalModel.Piece) : model.Piece := ⟨A.points,A.finite,A.closed⟩

theorem originalEmbedding_rootValue (A : originalModel.Piece)
    (f : A.Embedding Set.univ) (x : A.points) :
    f.point ⟨rootValue x.val,rootValue_closed A x⟩ = rootValue (f.point x) := by
  have hs : sort (f.point x) = sort x.val := f.sort_eq x
  by_cases h0 : sort x.val = 0
  · have hy : (⟨rootValue x.val,rootValue_closed A x⟩ : A.points) = A.func 2 x :=
      Subtype.ext (by change rootValue x.val = operation 2 x.val; simp [rootValue,h0])
    have ht : rootValue (f.point x) = operation 2 (f.point x) := by simp [rootValue,hs,h0]
    exact (congrArg f.point hy).trans ((f.func_eq 2 x).trans ht.symm)
  · by_cases h1 : sort x.val = 1
    · have hy : (⟨rootValue x.val,rootValue_closed A x⟩ : A.points) = A.func 1 x :=
        Subtype.ext (by change rootValue x.val = operation 1 x.val; simp [rootValue,h1])
      have ht : rootValue (f.point x) = operation 1 (f.point x) := by simp [rootValue,hs,h1]
      exact (congrArg f.point hy).trans ((f.func_eq 1 x).trans ht.symm)
    · have hy : (⟨rootValue x.val,rootValue_closed A x⟩ : A.points) = x :=
        Subtype.ext (by simp [rootValue,h0,h1])
      have ht : rootValue (f.point x) = f.point x := by simp [rootValue,hs,h0,h1]
      exact (congrArg f.point hy).trans ht.symm

theorem originalEmbedding_root_iff (A : originalModel.Piece)
    (f : A.Embedding Set.univ) (x y : A.points) :
    root (f.point x) = root (f.point y) ↔ root x.val = root y.val := by
  rw [root_eq_iff_values,root_eq_iff_values,
    ← originalEmbedding_rootValue A f x, ← originalEmbedding_rootValue A f y]
  exact f.injective.eq_iff.trans Subtype.ext_iff

/-- EVERY original closed partial embedding lifts with the SAME point map. -/
def expandedEmbedding {A : originalModel.Piece} (f : A.Embedding Set.univ) :
    (expandedPiece A).Embedding Set.univ where
  point := f.point
  mem_point := f.mem_point
  injective := f.injective
  sort_eq := f.sort_eq
  func_eq := f.func_eq
  rel_iff := by
    intro R xs
    change (sort (f.point (xs 0)) = R.1 ∧ sort (f.point (xs 1)) = R.2 ∧
      root (f.point (xs 0)) = root (f.point (xs 1))) ↔
      (sort (xs 0).val = R.1 ∧ sort (xs 1).val = R.2 ∧ root (xs 0).val = root (xs 1).val)
    have h0 : sort (f.point (xs 0)) = sort (xs 0).val := f.sort_eq _
    have h1 : sort (f.point (xs 1)) = sort (xs 1).val := f.sort_eq _
    rw [h0,h1,originalEmbedding_root_iff]

def originalAut (g : model.Aut) : originalModel.Aut :=
  ⟨g.val,g.property.1,g.property.2.1,(fun R => nomatch R)⟩

theorem original_homogeneous : originalModel.Homogeneous := by
  intro A f g
  obtain ⟨a,ha⟩ := homogeneous (expandedPiece A) (expandedEmbedding f) (expandedEmbedding g)
  exact ⟨originalAut a,ha⟩

theorem original_closure_eq (A : Set Point) : originalModel.closure A = model.closure A := by
  exact Set.Subset.antisymm
    (originalModel.closure_minimal (model.closure_closed A) (model.subset_closure A))
    (model.closure_minimal (originalModel.closure_closed A) (originalModel.subset_closure A))

theorem original_locallyFinite : originalModel.LocallyFinite := by
  intro A hA
  rw [original_closure_eq]
  exact locallyFinite A hA

theorem automorphisms_eq : originalModel.automorphisms = model.automorphisms := by
  ext e
  constructor
  · rintro ⟨hs,hf,_⟩
    have hs' (x : Point) : sort (e x) = sort x := hs x
    have hf' (F : Fin 4) (x : Point) : e (operation F x) = operation F (e x) := hf F x
    have hv (x : Point) : e (rootValue x) = rootValue (e x) := by
      unfold rootValue
      rw [hs' x]
      split_ifs
      · exact hf' 2 x
      · exact hf' 1 x
      · rfl
    have hroot (x y : Point) : root (e x) = root (e y) ↔ root x = root y := by
      rw [root_eq_iff_values,root_eq_iff_values,← hv x,← hv y]
      exact e.injective.eq_iff
    refine ⟨hs,hf,?_⟩
    intro R xs
    change (sort (e (xs 0)) = R.1 ∧ sort (e (xs 1)) = R.2 ∧ root (e (xs 0)) = root (e (xs 1))) ↔
      (sort (xs 0) = R.1 ∧ sort (xs 1) = R.2 ∧ root (xs 0) = root (xs 1))
    rw [hs',hs',hroot]
  · rintro ⟨hs,hf,_⟩
    exact ⟨hs,hf,(fun R => nomatch R)⟩

theorem original_real_base_orbits (D : Set Point) (hD : D.Finite)
    (hReal : ∀ x ∈ D, sort x = 0) (u : Point) (hu : u ∉ originalModel.closure D) :
    (orbitOver originalModel.Aut D u).Infinite := by
  rw [original_closure_eq] at hu
  change (orbitOver originalModel.automorphisms D u).Infinite
  rw [automorphisms_eq]
  exact real_base_orbits D hD hReal u hu

/-- Relations do not occur in unary term syntax; the actual named terms
translate in both directions without adding any map or factor. -/
noncomputable def expandTerm {i j : originalLanguage.Sorts} (t : Term originalLanguage i j) : Term language i j :=
  Term.rec (L := originalLanguage) (motive := fun k _ => Term language i k)
    (Term.id (L := language) i) (fun F _ ih => Term.func (L := language) F ih) t

noncomputable def originalTerm {i j : language.Sorts} (t : Term language i j) : Term originalLanguage i j :=
  Term.rec (L := language) (motive := fun k _ => Term originalLanguage i k)
    (Term.id (L := originalLanguage) i) (fun F _ ih => Term.func (L := originalLanguage) F ih) t

theorem expand_eval {i j : originalLanguage.Sorts} (t : Term originalLanguage i j) (x : Point) :
    model.eval (expandTerm t) x = originalModel.eval t x := by
  induction t with
  | id => rfl
  | func F t ih => exact congrArg (operation F) ih

theorem original_eval {i j : language.Sorts} (t : Term language i j) (x : Point) :
    originalModel.eval (originalTerm t) x = model.eval t x := by
  induction t with
  | id => rfl
  | func F t ih => exact congrArg (operation F) ih

/-- Actual forced factors in the ORIGINAL language, for BOTH named real
quotients τ and p, quantified over ALL actual real-source named terms. -/
theorem original_forced_named_factors {j : Fin 3} (t : Term originalLanguage 0 j) :
    ((∀ x y, sort x = 0 → sort y = 0 → operation 0 x = operation 0 y →
        originalModel.eval t x = originalModel.eval t y) →
      ∃ s : Term originalLanguage 1 j, ∀ x, sort x = 0 →
        originalModel.eval t x = originalModel.eval s (operation 0 x)) ∧
    ((∀ x y, sort x = 0 → sort y = 0 → operation 2 x = operation 2 y →
        originalModel.eval t x = originalModel.eval t y) →
      ∃ s : Term originalLanguage 2 j, ∀ x, sort x = 0 →
        originalModel.eval t x = originalModel.eval s (operation 2 x)) := by
  constructor
  · intro h
    have hf : ForcedBy 0 (expandTerm t) := by
      intro x y hx hy he
      rw [expand_eval,expand_eval]
      exact h x y hx hy he
    obtain ⟨s, hs⟩ := forced_tau_named_factor (expandTerm t) hf
    refine ⟨originalTerm s, ?_⟩
    intro x hx
    exact (expand_eval t x).symm.trans ((hs x hx).trans (original_eval s _).symm)
  · intro h
    have hf : ForcedBy 2 (expandTerm t) := by
      intro x y hx hy he
      rw [expand_eval,expand_eval]
      exact h x y hx hy he
    obtain ⟨s, hs⟩ := forced_p_named_factor (expandTerm t) hf
    refine ⟨originalTerm s, ?_⟩
    intro x hx
    exact (expand_eval t x).symm.trans ((hs x hx).trans (original_eval s _).symm)

theorem original_algebraic_off_closure (q : ℕ) (d : Bool) :
    middle q d ∈ Acl originalModel.Aut {rootPoint q} ∧
      middle q d ∉ originalModel.closureAt (rootPoint q) := by
  refine ⟨?_,?_⟩
  · change (orbitOver originalModel.automorphisms {rootPoint q} (middle q d)).Finite
    rw [automorphisms_eq,full_middle_orbit]
    exact (Set.finite_singleton _).insert _
  · change middle q d ∉ originalModel.closure {rootPoint q}
    rw [original_closure_eq]
    exact middle_off_root_closure q d

end CCO.UnaryFreshFrames.Examples.TwoCover
