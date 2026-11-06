import CCO.HiddenSAPReadings.OrbitalPullback

/-! Exact original fine-atom partition and all four genuine-Id exterior
cases. Every statement is CCO-free; positivity uses only old SAP and the
standing FULL original cover indices. -/

universe u v w r z t
namespace CCO.HiddenSAPReadings
open CCO.ParityHasse.Original CCO.TransitionClosure CCO.GroupActions
open CCO.QuotientTransport.SharedActions CCO.TypedOrbitFrames CCO.TerminalLattice
noncomputable section
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i : ι, MulAction G (X i)]
variable (H : HomogeneousSource S G)

/-- A true Id exterior is omitted from the STRONG word; it is never
replaced with the empty diversity palette. -/
def strongCylinder {i j : ι} (J : ColourEq S i) (K : ColourEq S j)
    (a : S.Atom i j) : S.Menu i j := by
  classical
  exact if J = ⊥ then
    if K = ⊥ then {a} else S.product {a} (originalEquivDiversityPalette S K)
  else if K = ⊥ then S.product (originalEquivDiversityPalette S J) {a}
  else S.product (originalEquivDiversityPalette S J)
    (S.product {a} (originalEquivDiversityPalette S K))

include H in
/-- C50: literal source saturation formula, including every Id case. -/
theorem cylinder_eq_strong_exteriors (sap : AgeSAP S) {i j : ι}
    (J : ColourEq S i) (K : ColourEq S j) (a : S.Atom i j) :
    originalTypedCylinderName S J K a = strongCylinder S J K a := by
  classical
  by_cases hJ : J = ⊥
  · subst J
    by_cases hK : K = ⊥
    · subst K
      simp only [strongCylinder,ite_true]
      change S.diversityGuard (originalRawTypedSandwich S ⊥ ⊥ a) = {a}
      rw [originalRawTypedSandwich_bot_both]
      exact original_raw_typed_no_exterior_guard_eq_atom S a
    · simp only [strongCylinder,ite_true,if_neg hK]
      change S.diversityGuard (originalRawTypedSandwich S ⊥ K a) = _
      rw [originalRawTypedSandwich_bot_left]
      exact original_raw_typed_right_exterior_guard_eq_strong S H sap K
        (lt_of_le_of_ne bot_le (Ne.symm hK)) a
  · by_cases hK : K = ⊥
    · subst K
      simp only [strongCylinder,if_neg hJ,ite_true]
      change S.diversityGuard (originalRawTypedSandwich S J ⊥ a) = _
      rw [originalRawTypedSandwich_bot_right]
      exact original_raw_typed_left_exterior_guard_eq_strong S H sap J
        (lt_of_le_of_ne bot_le (Ne.symm hJ)) a
    · simp only [strongCylinder,if_neg hJ,if_neg hK]
      exact original_raw_typed_J_atom_K_guard_eq_strong S H sap J K
        (lt_of_le_of_ne bot_le (Ne.symm hJ))
        (lt_of_le_of_ne bot_le (Ne.symm hK)) a

variable {i j : ι} {Q : Type z} {R : Type t}
variable [MulAction G Q] [MulAction G R]

/-- C57: every realized old diversity atom belongs to an output part. -/
theorem orbital_palettes_cover (τ : X i → Q) (σ : X j → R) :
    ∀ a : S.Atom i j, ∃ q r, a ∈ orbitalPalette (G := G) S τ σ q r := by
  intro a
  obtain ⟨x,y,hxy⟩ := S.realized a
  exact ⟨τ x,σ y,x,y,orbital_nonempty (τ x) (σ y),hxy⟩

include H in
/-- C58: common old atom forces equality of the COMPLETE output orbitals. -/
theorem orbital_palettes_overlap_eq
    (τ : X i → Q) (σ : X j → R)
    (equivτ : ∀ (g : G) x, τ (g • x) = g • τ x)
    (equivσ : ∀ (g : G) y, σ (g • y) = g • σ y)
    (q q' : Q) (r r' : R)
    (h : (orbitalPalette (G := G) S τ σ q r ∩ orbitalPalette (G := G) S τ σ q' r').Nonempty) :
    orbital (G := G) q r = orbital (G := G) q' r' := by
  obtain ⟨a,⟨x,y,hOutput,hxy⟩,⟨x',y',hOutput',hxy'⟩⟩ := h
  obtain ⟨g,hgx,hgy⟩ := S.pair_homogeneous_of_homogeneous H x x' y y'
    (hxy.trans hxy'.symm)
  have hMove := output_orbital_pullback_invariant τ σ equivτ equivσ q r g hOutput
  rw [hgx,hgy] at hMove
  exact orbital_eq_of_common_pair q q' (τ x') r r' (σ y') hMove hOutput'

include H in
theorem orbital_palettes_disjoint
    (τ : X i → Q) (σ : X j → R)
    (equivτ : ∀ (g : G) x, τ (g • x) = g • τ x)
    (equivσ : ∀ (g : G) y, σ (g • y) = g • σ y)
    (q q' : Q) (r r' : R)
    (hne : orbital (G := G) q r ≠ orbital (G := G) q' r') :
    Disjoint (orbitalPalette (G := G) S τ σ q r) (orbitalPalette (G := G) S τ σ q' r') := by
  rw [Set.disjoint_left]
  intro a ha ha'
  exact hne (orbital_palettes_overlap_eq S H τ σ equivτ equivσ q q' r r' ⟨a,ha,ha'⟩)

include H in
/-- C43/C59: at most one output orbital loses all old diversity. -/
theorem empty_orbital_palette_unique
    (τ : X i → Q) (σ : X j → R)
    (ontoτ : Function.Surjective τ) (ontoσ : Function.Surjective σ)
    (equivτ : ∀ (g : G) x, τ (g • x) = g • τ x)
    (equivσ : ∀ (g : G) y, σ (g • y) = g • σ y)
    (q q' : Q) (r r' : R)
    (h : orbitalPalette (G := G) S τ σ q r = ∅)
    (h' : orbitalPalette (G := G) S τ σ q' r' = ∅) :
    orbital (G := G) q r = orbital (G := G) q' r' := by
  obtain ⟨hij,hτ,hσ,hGraph⟩ :=
    (orbitalPalette_empty_iff S H τ σ ontoτ ontoσ equivτ equivσ q r).mp h
  cases hij
  obtain ⟨_,_,_,hGraph'⟩ :=
    (orbitalPalette_empty_iff S H τ σ ontoτ ontoσ equivτ equivσ q' r').mp h'
  exact hGraph.trans hGraph'.symm

include H in
/-- C45/C51: exact alternatives. Each nonempty part is one actual
positive STRONG word and the cylinder of ANY chosen witness atom. -/
theorem complete_orbital_diversity_dichotomy (sap : AgeSAP S)
    (hCover : ∀ k : ι, OriginalAllFullCoversInfinite S (i := k))
    (τ : X i → Q) (σ : X j → R)
    (ontoτ : Function.Surjective τ) (ontoσ : Function.Surjective σ)
    (equivτ : ∀ (g : G) x, τ (g • x) = g • τ x)
    (equivσ : ∀ (g : G) y, σ (g • y) = g • σ y)
    (q : Q) (r : R) :
    ((orbitalPalette (G := G) S τ σ q r).Nonempty ∧
      (∃ word : PositiveWord S i j,
        PositiveWord.profile S word = orbitalPalette (G := G) S τ σ q r) ∧
      ∀ (a : S.Atom i j) (x : X i) (y : X j),
        S.atomRel a x y → orbital (G := G) q r (τ x) (σ y) →
        orbitalPalette (G := G) S τ σ q r =
          originalTypedCylinderName S (equivariantKernel S H τ equivτ)
            (equivariantKernel S H σ equivσ) a) ∨
    (orbitalPalette (G := G) S τ σ q r = ∅ ∧
      RealIdentityException (X := X) (G := G) τ σ q r) := by
  classical
  by_cases hNonempty : (orbitalPalette (G := G) S τ σ q r).Nonempty
  · obtain ⟨a,x,y,hOutput,hxy⟩ := hNonempty
    obtain ⟨hn,hCylinder,hPositive⟩ := complete_orbital_positive_pullback
      S H sap hCover τ σ equivτ equivσ q r a x y hxy hOutput
    exact Or.inl ⟨hn,hPositive,
      fun b x' y' hxy' hOutput' => orbitalPalette_eq_cylinder
        S H τ σ equivτ equivσ q r b x' y' hxy' hOutput'⟩
  · have hEmpty : orbitalPalette (G := G) S τ σ q r = ∅ := Set.not_nonempty_iff_eq_empty.mp hNonempty
    exact Or.inr ⟨hEmpty,
      (orbitalPalette_empty_iff S H τ σ ontoτ ontoσ equivτ equivσ q r).mp hEmpty⟩

end
end CCO.HiddenSAPReadings
