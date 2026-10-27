import CCO.ActionBridge
import CCO.AtomicPeirce

/-!
# Finite homogeneous source gives actual one-point and two-point orbitals

A complete atomic *tuple* records the logical diagonal as `none`.
Thus finite tuple homogeneity applies also when the two indexed slots
refer to the same original point. No invented identity diversity colour
is introduced. These theorems use the canonical action on `Sigma X`.
-/

universe u v w

namespace CCO.AtomicSource

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource ι X)

/-- Correctly typed reversal of the actual optional pair colour,
including the true real diagonal. -/
theorem colour_reverse {i j : ι} (x : X i) (y : X j) :
    S.colour y x = (S.colour x y).map (fun a => S.conv a) := by
  cases hc : S.colour x y with
  | none =>
      simp only [hc, Option.map_none]
      exact (S.colour_none_iff y x).mpr
        ((S.colour_none_iff x y).mp hc).symm
  | some a =>
      simp only [hc, Option.map_some]
      exact (S.colour_swap x y a).mp hc

section Homogeneous

variable {G : Type*} [Group G]
variable [∀ i : ι, MulAction G (X i)]

/-- Real pair homogeneity derived from the finite complete homogeneous
source, including same-sort pairs, cross-sort pairs and the diagonal. -/
theorem pair_homogeneous_of_homogeneous
    (H : HomogeneousSource S G) {i j : ι} :
    S.PairHomogeneous (G := G) (i := i) (j := j) := by
  intro x x' y y' hxy
  have hrev : S.colour y x = S.colour y' x' := by
    calc
      S.colour y x = (S.colour x y).map (fun a => S.conv a) :=
        S.colour_reverse x y
      _ = (S.colour x' y').map (fun a => S.conv a) := by
        rw [hxy]
      _ = S.colour y' x' := (S.colour_reverse x' y').symm
  have hxx : S.colour x x = S.colour x' x' := by
    calc
      S.colour x x = none := (S.colour_none_iff x x).mpr rfl
      _ = S.colour x' x' := ((S.colour_none_iff x' x').mpr rfl).symm
  have hyy : S.colour y y = S.colour y' y' := by
    calc
      S.colour y y = none := (S.colour_none_iff y y).mpr rfl
      _ = S.colour y' y' := ((S.colour_none_iff y' y').mpr rfl).symm
  let f : ULift.{max u v} Bool → Sigma X :=
    fun b => if b.down then ⟨j, y⟩ else ⟨i, x⟩
  let h : ULift.{max u v} Bool → Sigma X :=
    fun b => if b.down then ⟨j, y'⟩ else ⟨i, x'⟩
  have hpairs : ∀ a b : ULift.{max u v} Bool,
      taggedColour S (f a) (f b) = taggedColour S (h a) (h b) := by
    intro ⟨a⟩ ⟨b⟩
    cases a <;> cases b <;>
      simp [f, h, taggedColour, hxx, hxy, hrev, hyy]
  obtain ⟨g, hg⟩ :=
    H.extends_finite_diagram (V := ULift.{max u v} Bool) f h hpairs
  refine ⟨g, ?_, ?_⟩
  · have htag : (⟨i, g • x⟩ : Sigma X) = ⟨i, x'⟩ := by
      simpa [f, h] using (hg ⟨false⟩)
    simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using htag
  · have htag : (⟨j, g • y⟩ : Sigma X) = ⟨j, y'⟩ := by
      simpa [f, h] using (hg ⟨true⟩)
    simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using htag

/-- In particular the named original group action is transitive on
every inhabited sort; this is derived, not postulated. -/
theorem original_sort_transitive_of_homogeneous
    (H : HomogeneousSource S G) (i : ι) :
    ∀ x y : X i, ∃ g : G, g • x = y := by
  intro x y
  have hc : S.colour x x = S.colour y y := by
    calc
      S.colour x x = none := (S.colour_none_iff x x).mpr rfl
      _ = S.colour y y := ((S.colour_none_iff y y).mpr rfl).symm
  obtain ⟨g, hg, _⟩ :=
    (S.pair_homogeneous_of_homogeneous H (i := i) (j := i)) x y x y hc
  exact ⟨g, hg⟩

/-- Every actual diversity atom is its complete ordered-pair group
orbital. The only hypotheses are those of the original homogeneous
source, not SAP or CCO. -/
theorem diversity_atom_is_orbital_of_homogeneous
    (H : HomogeneousSource S G) {i j : ι} (a : S.Atom i j) :
    ∃ x₀ : X i, ∃ y₀ : X j,
      S.atomRel a x₀ y₀ ∧
        S.atomRel a = GroupActions.orbital (G := G) x₀ y₀ :=
  S.atom_is_actual_orbital a
    (S.colourInvariant_of_homogeneous H)
    (S.pair_homogeneous_of_homogeneous H)

/-- Finite homogeneous symmetric atomic colours give simultaneous flips
of all ordered same-sort pairs, the precise scope needed for RAW joins. -/
theorem pair_flip_of_homogeneous
    (H : HomogeneousSource S G) {i : ι} :
    RawSymmetric.PairFlip (G := G) (A := X i) :=
  S.pair_flip_of_pair_homogeneous
    (S.pair_homogeneous_of_homogeneous H (i := i) (j := i))

end Homogeneous
end CCO.AtomicSource
