import CCO.ParityHasse.Original.ParitySeed
import CCO.ParityHasse.Original.GraphBipartite
import CCO.ParityHasse.Sparse.Existence
import CCO.ParityHasse.Original.HassePowers
import Mathlib.Tactic.Push

/-! Assemble the actual SAP-free source parity seed and full-lattice Hasse
induction. The independent sparse graph construction is the only remaining
combinatorial input of this assembly layer. -/
universe u v w t
namespace CCO.ParityHasse.Original
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X) {i : ι}
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

/-- The cardinal transposition is discharged by a natural class bijection,
separately from the actual modular-lattice interval isomorphism. -/
theorem source_index_transposition (H : HomogeneousSource S G)
    (E K : ColourEq S i) (a : X i) :
    relativeIndex (E ⊓ K).val K.val a =
      relativeIndex E.val (ColourEq.join S H E K).val a := by
  apply relativeIndex_transposition E.val K.val
  intro x y
  rw [sup_comm]
  exact sup_relation_iff S H K E x y

/-- Any strict full invariant interval has a genuine old diversity atom
in its difference, with the whole represented atom in that difference. -/
theorem exists_atom_difference (E F : ColourEq S i) (hEF : E < F) :
    ∃ c : S.Atom i i, ∀ x y, S.atomRel c x y → F x y ∧ ¬ E x y := by
  classical
  have hnot : ¬ F ≤ E := hEF.not_ge
  change ¬ ∀ ⦃x y⦄, F x y → E x y at hnot
  push Not at hnot
  obtain ⟨x,y,hF,hE⟩ := hnot
  cases hc : S.colour x y with
  | none =>
    have hxy : x = y := by
      have h := (S.colour_none_iff x y).mp hc
      simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using h
    exact False.elim (hE (hxy ▸ E.val.refl x))
  | some c =>
    refine ⟨c, ?_⟩
    intro x' y' hc'
    have hh : S.colour x y = S.colour x' y' := hc.trans hc'.symm
    exact ⟨(F.2 x y x' y' hh).mp hF, fun he => hE ((E.2 x y x' y' hh).mpr he)⟩

/-- A real finite-relative interval supplies a real parity seed; all
NoOdd/word/profile/class data are constructed from H+CCO and sparse graphs. -/
theorem actual_parity_seed_from_sparse (H : HomogeneousSource S G)
    (cco : SemanticCCO.{u,v,0,w} S)
    (sparse : ∀ q g : Nat, 0 < q → 0 < g →
      Nonempty (Sparse.ConnectedHighGirthChromatic q g))
    (E F : ColourEq S i) (hEF : E < F) (a : X i)
    [Finite (RelativeClass E.val F.val a)] :
    ∃ Y K : ColourEq S i,
      Y ⋖ K ∧ K ≤ F ∧ ¬K ≤ E ∧ relativeIndex Y.val K.val a = 2 := by
  obtain ⟨c, hc⟩ := exists_atom_difference S E F hEF
  have hw := no_odd_orbital_walk_from_sparse S H cco sparse E F a c hc
  have noOdd : ∀ x n, Odd n → ¬relPow (S.atomRel c) n x x := by
    intro x n hn hp
    obtain ⟨p, hpn⟩ := (relPow_atom_iff_walk S c n x x).mp hp
    exact hw x p (by simpa only [hpn] using hn)
  obtain ⟨Y,K,_,hidx,hcov,hF,hE⟩ := exists_actual_parity_seed S H c noOdd a
  exact ⟨Y,K,hcov,hF F (fun x y h => (hc x y h).1),
    hE E (fun x y h => (hc x y h).2),hidx⟩

/-- Full finite-relative covers have index two, not merely covers in an
exact-equivalence sublattice. -/
theorem full_relative_hasse_from_sparse (H : HomogeneousSource S G)
    (cco : SemanticCCO.{u,v,0,w} S)
    (sparse : ∀ q g : Nat, 0 < q → 0 < g →
      Nonempty (Sparse.ConnectedHighGirthChromatic q g))
    (E F : ColourEq S i) (hEF : E ⋖ F) (a : X i)
    [Finite (RelativeClass E.val F.val a)] :
    relativeIndex E.val F.val a = 2 := by
  letI := ColourEq.lattice S H (i := i)
  letI := ColourEq.modular S H (i := i)
  let idx := fun E F : ColourEq S i => relativeIndex E.val F.val a
  apply finiteRelativeHasseInduction idx
    (fun E X => source_index_transposition S H E X a) ?_ E F hEF
    (Nat.ne_of_gt Nat.card_pos)
  intro E F hcover hfin
  have hpos : 0 < relativeIndex E.val F.val a := Nat.pos_of_ne_zero hfin
  letI : Finite (RelativeClass E.val F.val a) := (Nat.card_pos_iff.mp hpos).2
  exact actual_parity_seed_from_sparse S H cco sparse E F hcover.lt a

/-- All finite relative indices are powers of two; equality gives 2^0. -/
theorem finite_relative_power_two_from_sparse (H : HomogeneousSource S G)
    (cco : SemanticCCO.{u,v,0,w} S)
    (sparse : ∀ q g : Nat, 0 < q → 0 < g →
      Nonempty (Sparse.ConnectedHighGirthChromatic q g))
    (E F : ColourEq S i) (hEF : E ≤ F) (a : X i)
    [Finite (RelativeClass E.val F.val a)] :
    ∃ n : Nat, relativeIndex E.val F.val a = 2^n := by
  let idx := fun E F : ColourEq S i => relativeIndex E.val F.val a
  apply relativeIndicesPowerTwo idx (fun E => relativeIndex_self E.val a) ?_ ?_
    E F hEF (Nat.ne_of_gt Nat.card_pos)
  · intro E D F hED hDF hfin
    have hpos : 0 < relativeIndex E.val F.val a := Nat.pos_of_ne_zero hfin
    letI : Finite (RelativeClass E.val F.val a) := (Nat.card_pos_iff.mp hpos).2
    exact relativeIndex_mul S H E D F hED hDF a
  · intro E F hcover hfin
    have hpos : 0 < relativeIndex E.val F.val a := Nat.pos_of_ne_zero hfin
    letI : Finite (RelativeClass E.val F.val a) := (Nat.card_pos_iff.mp hpos).2
    exact full_relative_hasse_from_sparse S H cco sparse E F hcover a

/-- The proved finite combinatorial construction, with no graph provider premise. -/
theorem source_sparse_graphs (q g : Nat) (hq : 0 < q) (_hg : 0 < g) :
    Nonempty (Sparse.ConnectedHighGirthChromatic q g) :=
  Sparse.connected_high_girth_chromatic_exists hq g

/-- Original finite-relative orbital parity from the actual sparse graph
construction and semantic CCO, with no additional source provider. -/
theorem no_odd_orbital_walk (H : HomogeneousSource S G)
    (cco : SemanticCCO.{u,v,0,w} S)
    (E F : ColourEq S i) (a : X i)
    [Finite (RelativeClass E.val F.val a)] (c : S.Atom i i)
    (hFE : ∀ x y, S.atomRel c x y → F x y ∧ ¬E x y) :
    ∀ x (p : (atomGraph S c).Walk x x), ¬Odd p.length :=
  no_odd_orbital_walk_from_sparse S H cco source_sparse_graphs E F a c hFE

/-- C10: the actual old orbital graph admits a genuine two-colouring. -/
theorem orbital_bipartite (H : HomogeneousSource S G)
    (cco : SemanticCCO.{u,v,0,w} S)
    (E F : ColourEq S i) (a : X i)
    [Finite (RelativeClass E.val F.val a)] (c : S.Atom i i)
    (hFE : ∀ x y, S.atomRel c x y → F x y ∧ ¬E x y) :
    (atomGraph S c).IsBipartite :=
  no_odd_closed_walk_isBipartite (atomGraph S c)
    (no_odd_orbital_walk S H cco E F a c hFE)

/-- C11/C12: the SAME actual orbital supplies the full parity seed,
including its genuine positive-word representations and non-exact
connectivity upper endpoint. No NoOdd or graph provider remains. -/
theorem source_orbital_parity (H : HomogeneousSource S G)
    (cco : SemanticCCO.{u,v,0,w} S)
    (E F : ColourEq S i) (a : X i)
    [Finite (RelativeClass E.val F.val a)] (c : S.Atom i i)
    (hFE : ∀ x y, S.atomRel c x y → F x y ∧ ¬E x y) :
    evenColourEq S H c ⋖ connectivityColourEq S H c ∧
    relativeIndex (evenColourEq S H c).val (connectivityColourEq S H c).val a = 2 ∧
    connectivityColourEq S H c ≤ F ∧ ¬connectivityColourEq S H c ≤ E ∧
    (∀ x y, connectivityColourEq S H c x y ↔
      evenColourEq S H c x y ∨ OddWalk (S.atomRel c) x y) ∧
    (∃ N : Nat, 0 < N ∧
      (∀ x y, evenColourEq S H c x y ↔
        RawWord.relation S (atomWord S c (2*N)) x y) ∧
      (∀ x y, OddWalk (S.atomRel c) x y ↔
        RawWord.relation S (atomWord S c (2*N+1)) x y)) := by
  have noOdd : ∀ x n, Odd n → ¬relPow (S.atomRel c) n x x := by
    intro x n hn hp
    obtain ⟨p, hpn⟩ := (relPow_atom_iff_walk S c n x x).mp hp
    exact no_odd_orbital_walk S H cco E F a c hFE x p (by simpa only [hpn] using hn)
  exact ⟨parity_seed_cover S H c noOdd, parity_seed_index_two S H c noOdd a,
    connectivity_le_of_atom_le S H c F (fun x y h => (hFE x y h).1),
    connectivity_not_le_of_atom_disjoint S H c E (fun x y h => (hFE x y h).2),
    connectivity_eq_even_union_odd S H c, parity_profiles_positive_raw S H c⟩

/-- A genuine index-two parity seed in any finite relative full interval. -/
theorem actual_parity_seed (H : HomogeneousSource S G)
    (cco : SemanticCCO.{u,v,0,w} S)
    (E F : ColourEq S i) (hEF : E < F) (a : X i)
    [Finite (RelativeClass E.val F.val a)] :
    ∃ Y K : ColourEq S i,
      Y ⋖ K ∧ K ≤ F ∧ ¬K ≤ E ∧ relativeIndex Y.val K.val a = 2 :=
  actual_parity_seed_from_sparse S H cco source_sparse_graphs E F hEF a

/-- C13, full source theorem. Neither endpoint is assumed exact. -/
theorem full_relative_hasse (H : HomogeneousSource S G)
    (cco : SemanticCCO.{u,v,0,w} S)
    (E F : ColourEq S i) (hEF : E ⋖ F) (a : X i)
    [Finite (RelativeClass E.val F.val a)] :
    relativeIndex E.val F.val a = 2 :=
  full_relative_hasse_from_sparse S H cco source_sparse_graphs E F hEF a

/-- C14, full source theorem, with equality giving 1=2^0. -/
theorem finite_relative_power_two (H : HomogeneousSource S G)
    (cco : SemanticCCO.{u,v,0,w} S)
    (E F : ColourEq S i) (hEF : E ≤ F) (a : X i)
    [Finite (RelativeClass E.val F.val a)] :
    ∃ n : Nat, relativeIndex E.val F.val a = 2^n :=
  finite_relative_power_two_from_sparse S H cco source_sparse_graphs E F hEF a

end CCO.ParityHasse.Original
