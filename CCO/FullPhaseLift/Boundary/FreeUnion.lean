import CCO.FullPhaseLift.Boundary.Hypergraph

/-! Free unions preserve the actual K₄³-free condition. The proof retains
all full triples in each leg and uses the absence of cross triples; it
does not infer a full-language completion theorem from the pure pair age. -/

universe u v w
namespace CCO.FullPhaseLift.Boundary

private theorem clique_in_factor {A : Type u} {V : Type v}
    (R : TripleRelation V) (RA : TripleRelation A) (l : A → V)
    (hA : K4Free RA)
    (hl : ∀ a b c, R (l a) (l b) (l c) ↔ RA a b c)
    (f : Fin 4 → V) (hf : Function.Injective f)
    (hcl : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → R (f i) (f j) (f k))
    (hinto : ∀ i, ∃ a, l a = f i) : False := by
  classical
  let g : Fin 4 → A := fun i => (hinto i).choose
  have hg (i) : l (g i) = f i := (hinto i).choose_spec
  have hi : Function.Injective g := by
    intro i j h
    exact hf ((hg i).symm.trans ((congrArg l h).trans (hg j)))
  apply hA g hi
  intro i j k hij hik hjk
  apply (hl _ _ _).mp
  rw [hg i,hg j,hg k]
  exact hcl i j k hij hik hjk

/-- A free union of two induced K₄³-free factors remains K₄³-free,
regardless of the size of their common part. -/
theorem k4Free_of_two_factors {A : Type u} {B : Type v} {V : Type w}
    (R : TripleRelation V) (RA : TripleRelation A) (RB : TripleRelation B)
    (l : A → V) (r : B → V) (hA : K4Free RA) (hB : K4Free RB)
    (hl : ∀ a b c, R (l a) (l b) (l c) ↔ RA a b c)
    (hr : ∀ a b c, R (r a) (r b) (r c) ↔ RB a b c)
    (cover : ∀ x, (∃ a, l a = x) ∨ (∃ b, r b = x))
    (tuple_local : ∀ x y z, R x y z →
      ((∃ a, l a = x) ∧ (∃ b, l b = y) ∧ (∃ c, l c = z)) ∨
      ((∃ a, r a = x) ∧ (∃ b, r b = y) ∧ (∃ c, r c = z))) : K4Free R := by
  classical
  intro f hf hcl
  by_cases hleft : ∀ i, ∃ a, l a = f i
  · exact clique_in_factor R RA l hA hl f hf hcl hleft
  by_cases hright : ∀ i, ∃ b, r b = f i
  · exact clique_in_factor R RB r hB hr f hf hcl hright
  obtain ⟨i,hi⟩ := not_forall.mp hleft
  obtain ⟨j,hj⟩ := not_forall.mp hright
  have hij : i ≠ j := by
    intro he
    rcases cover (f i) with h | h
    · exact hi h
    · exact hj (he ▸ h)
  have third : ∀ i j : Fin 4, ∃ k, k ≠ i ∧ k ≠ j := by decide
  obtain ⟨k,hki,hkj⟩ := third i j
  rcases tuple_local (f i) (f j) (f k) (hcl i j k hij hki.symm hkj.symm) with h | h
  · exact hi h.1
  · exact hj h.2.1

end CCO.FullPhaseLift.Boundary
