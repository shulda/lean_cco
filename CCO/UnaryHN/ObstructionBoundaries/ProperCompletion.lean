import CCO.UnaryHN.ObstructionBoundaries.ProtectedPieces

/-! Every proper actual induced subset completes on its OWN carrier. A
missing vertex cuts the R-chain; the two resulting sides can be merged
within each side, while all protected irreducibles remain induced. -/
universe u v
namespace CCO.UnaryHN.Native.ObstructionBoundaries
open StructuralRamsey
open StructuralRamsey.Structure

/-- Positive maps between completed networks reflect both colors and are
injective: every distinct pair carries exactly one positive color. -/
def networkPositiveEmbedding {V : Type u} {W : Type v} (E : Setoid V) (F : Setoid W)
    (f : V → W) (h : ∀ color xs, (network E).rel color xs → (network F).rel color (f ∘ xs)) :
    Embedding (network E) (network F) where
  toFun := f
  injective := by
    intro x y heq
    by_contra hne
    obtain ⟨color, hColor⟩ := network_coverage E hne
    have hp := h color ![x, y] hColor
    have hl : (network F).rel color ![f x, f x] := by
      cases color <;> simpa only [network, Function.comp_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, heq] using hp
    exact network_irreflexive F color (f x) hl
  map_rel_iff := by
    intro color xs
    constructor
    · intro hp
      cases color
      · change F.r (f (xs 0)) (f (xs 1)) ∧ f (xs 0) ≠ f (xs 1) at hp
        change E.r (xs 0) (xs 1) ∧ xs 0 ≠ xs 1
        refine ⟨?_, fun heq => hp.2 (congrArg f heq)⟩
        by_contra hE
        exact (h true xs hE) hp.1
      · change ¬ F.r (f (xs 0)) (f (xs 1)) at hp
        change ¬ E.r (xs 0) (xs 1)
        intro hE
        by_cases hxy : xs 0 = xs 1
        · exact hp (by simpa only [hxy] using F.refl (f (xs 1)))
        · exact hp (h false xs ⟨hE, hxy⟩).1
    · exact h color xs
  map_func F := Empty.elim F

def completedPositiveEmbedding {V : Type u} {W : Type v} {C : Diagram V} {D : Diagram W}
    (hC : completed C) (hD : completed D) (f : V → W)
    (h : ∀ color xs, C.rel color xs → D.rel color (f ∘ xs)) : Embedding C D where
  toFun := f
  injective := by
    obtain ⟨_, E, rfl⟩ := hC
    obtain ⟨_, F, rfl⟩ := hD
    exact (networkPositiveEmbedding E F f h).injective
  map_rel_iff := by
    obtain ⟨_, E, rfl⟩ := hC
    obtain ⟨_, F, rfl⟩ := hD
    exact (networkPositiveEmbedding E F f h).map_rel_iff
  map_func F := Empty.elim F

/-- Actual K-membership of all protected pieces upgrades the positive map
on this source to a native HE. It does not impose global inducedness. -/
theorem positive_HE {V W : Type u} {C : Diagram V} {D : Diagram W}
    (hC : IrreduciblesIn completed C) (hD : completed D) (f : V → W)
    (h : ∀ color xs, C.rel color xs → D.rel color (f ∘ xs)) : HE C D f := by
  refine ⟨⟨h, fun F => Empty.elim F⟩, ?_⟩
  intro X E hE e
  exact ⟨completedPositiveEmbedding (hC E hE e) hD (f ∘ e)
    (fun color xs hx => h color (e ∘ xs) ((e.map_rel_iff color xs).mpr hx)), fun _ => rfl⟩

def cutLabel {n : ℕ} (j : Fin n) (S : Set (Fin n)) (x : S) : Bool := decide (x.val.val < j.val)

theorem path_cut_positive {n : ℕ} (j : Fin n) (S : Set (Fin n)) (hj : j ∉ S) :
    ∀ color xs,
      ((path n).induce S (every_set_closed _ S)).rel color xs →
        (network (Setoid.ker (cutLabel j S))).rel color xs := by
  intro color xs hp
  have hx : (xs 0).val ≠ j := fun h => hj (h ▸ (xs 0).property)
  have hy : (xs 1).val ≠ j := fun h => hj (h ▸ (xs 1).property)
  have hxv : (xs 0).val.val ≠ j.val := fun h => hx (Fin.ext h)
  have hyv : (xs 1).val.val ≠ j.val := fun h => hy (Fin.ext h)
  cases color
  · change Adjacent (xs 0).val (xs 1).val at hp
    change cutLabel j S (xs 0) = cutLabel j S (xs 1) ∧ xs 0 ≠ xs 1
    constructor
    · apply decide_eq_decide.mpr
      unfold Adjacent at hp
      omega
    · intro h
      have hv := congrArg (fun x : S => x.val.val) h
      unfold Adjacent at hp
      omega
  · change Endpoints (xs 0).val (xs 1).val at hp
    change cutLabel j S (xs 0) ≠ cutLabel j S (xs 1)
    intro h
    have hh : (xs 0).val.val < j.val ↔ (xs 1).val.val < j.val := decide_eq_decide.mp h
    have hxLt := (xs 0).val.isLt
    have hyLt := (xs 1).val.isLt
    have hjLt := j.isLt
    unfold Endpoints at hp
    omega

/-- Every proper actual induced substructure, of every cardinality,
has a globally injective homomorphism-embedding completion. -/
theorem every_proper_subset_completes {n : ℕ} (hn : 4 ≤ n) (S : Set (Fin n))
    (hProper : S ≠ Set.univ) :
    HasStrongCompletion completed ((path n).induce S (every_set_closed _ S)) := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, j ∉ S := by
    by_contra! h
    exact hProper (Set.eq_univ_of_forall h)
  let T := network (Setoid.ker (cutLabel j S))
  have hT : completed T := completed_network _
  have hPieces : IrreduciblesIn completed ((path n).induce S (every_set_closed _ S)) := by
    intro X E hE e
    exact path_irreducibles_completed hn E hE ((inclusion _ S _).comp e)
  refine ⟨S, inferInstance, T, hT, id, ?_, Function.injective_id⟩
  apply positive_HE hPieces hT id
  exact path_cut_positive j S hj

end CCO.UnaryHN.Native.ObstructionBoundaries
