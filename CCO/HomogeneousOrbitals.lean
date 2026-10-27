import CCO.ActionBridge
import CCO.AtomicPeirce

/-!
# Actual original-sort transitivity and pair orbitals from finite homogeneity

The finite-complete-tuple extension property is the ONE source premise.
The same group acts on the named-sort carriers and their canonical tagged
sum, so no independent orbit-uniformity or pair-flip axiom is imposed.
-/

namespace CCO.AtomicSource

variable {ι : Type*} {X : ι → Type*}
variable (S : AtomicSource ι X)

/-- Typed optional atomic converse, including the real diagonal. -/
theorem reverse_colour {i j : ι} (x : X i) (y : X j) :
    S.colour y x = Option.map (fun a => S.conv a) (S.colour x y) := by
  cases hc : S.colour x y with
  | none =>
      have htag : (⟨i, x⟩ : Sigma X) = ⟨j, y⟩ :=
        (S.colour_none_iff x y).mp hc
      have hback : S.colour y x = none :=
        (S.colour_none_iff y x).mpr htag.symm
      simp only [hc, Option.map_none, hback]
  | some a =>
      have hback : S.colour y x = some (S.conv a) :=
        (S.colour_swap x y a).mp hc
      simp only [hc, Option.map_some, hback]

section ActualGroup

variable {G : Type*} [Group G] [∀ i : ι, MulAction G (X i)]

/-- Every colour-preserving map of a two-entry *actual* tuple extends.
In particular the map may identify its entries on either side exactly
when the source atom is the logical diagonal; no spurious diversity
identity is inserted. -/
theorem pairHomogeneous_of_homogeneous
    (H : HomogeneousSource S G)
    {i j : ι} :
    S.PairHomogeneous (G := G) (i := i) (j := j) := by
  intro x x' y y' hxy
  let f : Fin 2 → Sigma X := fun v =>
    if v.val = 0 then ⟨i, x⟩ else ⟨j, y⟩
  let t : Fin 2 → Sigma X := fun v =>
    if v.val = 0 then ⟨i, x'⟩ else ⟨j, y'⟩
  have hrev : S.colour y x = S.colour y' x' := by
    rw [S.reverse_colour x y, S.reverse_colour x' y', hxy]
  have hpair : ∀ v w, taggedColour S (f v) (f w) =
      taggedColour S (t v) (t w) := by
    intro v w
    fin_cases v <;> fin_cases w
    · change (⟨i, i, S.colour x x⟩ :
          Σ k : ι, Σ l : ι, Option (S.Atom k l)) =
        ⟨i, i, S.colour x' x'⟩
      have hx : S.colour x x = none :=
        (S.colour_none_iff x x).mpr rfl
      have hx' : S.colour x' x' = none :=
        (S.colour_none_iff x' x').mpr rfl
      simp only [hx, hx']
    · change (⟨i, j, S.colour x y⟩ :
          Σ k : ι, Σ l : ι, Option (S.Atom k l)) =
        ⟨i, j, S.colour x' y'⟩
      rw [hxy]
    · change (⟨j, i, S.colour y x⟩ :
          Σ k : ι, Σ l : ι, Option (S.Atom k l)) =
        ⟨j, i, S.colour y' x'⟩
      rw [hrev]
    · change (⟨j, j, S.colour y y⟩ :
          Σ k : ι, Σ l : ι, Option (S.Atom k l)) =
        ⟨j, j, S.colour y' y'⟩
      have hy : S.colour y y = none :=
        (S.colour_none_iff y y).mpr rfl
      have hy' : S.colour y' y' = none :=
        (S.colour_none_iff y' y').mpr rfl
      simp only [hy, hy']
  obtain ⟨g, hg⟩ := H.extends_finite_diagram f t hpair
  refine ⟨g, ?_, ?_⟩
  · have htag : (⟨i, g • x⟩ : Sigma X) = ⟨i, x'⟩ := by
      simpa only [f, t, Sigma.smul_mk, Fin.val_zero, Nat.reduceEqDiff,
        ite_true] using (hg (0 : Fin 2))
    simpa only [Sigma.mk.injEq, eq_self_iff_true, true_and] using htag
  · have htag : (⟨j, g • y⟩ : Sigma X) = ⟨j, y'⟩ := by
      simpa [f, t, Sigma.smul_mk] using (hg (1 : Fin 2))
    simpa only [Sigma.mk.injEq, eq_self_iff_true, true_and] using htag

/-- Point transitivity is a *consequence* of actual finite homogeneity,
not a further homogeneous-source hypothesis. -/
theorem transitive_of_homogeneous (H : HomogeneousSource S G)
    (i : ι) (x y : X i) : ∃ g : G, g • x = y := by
  have hx : S.colour x x = none :=
    (S.colour_none_iff x x).mpr rfl
  have hy : S.colour y y = none :=
    (S.colour_none_iff y y).mpr rfl
  obtain ⟨g, hg, _⟩ :=
    (S.pairHomogeneous_of_homogeneous H (i := i) (j := i))
      x y x y (hx.trans hy.symm)
  exact ⟨g, hg⟩

/-- Same-sort commutation no longer needs an independent symmetry
provider once an actual homogeneous source has been supplied. -/
theorem pairFlip_of_homogeneous (H : HomogeneousSource S G)
    (i : ι) :
    RawSymmetric.PairFlip (G := G) (A := X i) :=
  S.pair_flip_of_pair_homogeneous
    (S.pairHomogeneous_of_homogeneous H (i := i) (j := i))

end ActualGroup
end CCO.AtomicSource
