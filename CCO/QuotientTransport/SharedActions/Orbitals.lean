import CCO.GroupQuotient

/-! B040 C33–C44: full actual orbital pullbacks, followed by real diversity.
These are explicit consumers of shared B001 `GroupActions`/`GroupQuotient`;
their ownership and all existing imports remain unchanged. -/

namespace CCO.QuotientTransport.SharedActions

open GroupActions

section General

variable {G A B Q R : Type*} [Group G]
variable [MulAction G A] [MulAction G B] [MulAction G Q] [MulAction G R]

/-- C33: kernels are actual invariant equivalences. -/
theorem kernel_equivalence_invariant (τ : A → Q)
    (equivariant : ∀ (g : G) x, τ (g • x) = g • τ x) :
    Equivalence (kernel τ) ∧
      (∀ (g : G) x y, kernel τ x y → kernel τ (g • x) (g • y)) := by
  refine ⟨⟨fun _ => rfl, fun h => h.symm, fun h k => h.trans k⟩, ?_⟩
  intro g x y h
  change τ (g • x) = τ (g • y)
  rw [equivariant, equivariant, h]

omit [MulAction G A] [MulAction G B] in
/-- C33: every output orbital has an actual root pair, possibly diagonal. -/
theorem output_orbital_has_root_witness (τ : A → Q) (σ : B → R)
    (ontoτ : Function.Surjective τ) (ontoσ : Function.Surjective σ)
    (q : Q) (r : R) : ∃ a b, pullback τ σ (orbital (G := G) q r) a b := by
  obtain ⟨a, ha⟩ := ontoτ q
  obtain ⟨b, hb⟩ := ontoσ r
  exact ⟨a, b, by rw [pullback, ha, hb]; exact orbital_nonempty q r⟩

/-- C33: pullback is invariant under the SAME original group element. -/
theorem output_orbital_pullback_invariant (τ : A → Q) (σ : B → R)
    (equivτ : ∀ (g : G) x, τ (g • x) = g • τ x)
    (equivσ : ∀ (g : G) y, σ (g • y) = g • σ y)
    (q : Q) (r : R) (g : G) {x : A} {y : B}
    (h : pullback τ σ (orbital (G := G) q r) x y) :
    pullback τ σ (orbital (G := G) q r) (g • x) (g • y) := by
  change orbital (G := G) q r (τ (g • x)) (σ (g • y))
  rw [equivτ, equivσ]
  exact orbital_invariant q r h g

/-- C34/C35: saturation for ANY root witness, with its full root orbital. -/
theorem saturation_of_any_root_witness (τ : A → Q) (σ : B → R)
    (equivτ : ∀ (g : G) x, τ (g • x) = g • τ x)
    (equivσ : ∀ (g : G) y, σ (g • y) = g • σ y)
    {q : Q} {r : R} {a : A} {b : B}
    (witness : pullback τ σ (orbital (G := G) q r) a b) :
    pullback τ σ (orbital (G := G) q r) =
      saturation τ σ (orbital (G := G) a b) := by
  have same : orbital (G := G) q r = orbital (G := G) (τ a) (σ b) :=
    orbital_eq_of_mem q r (τ a) (σ b) witness
  rw [same]
  exact orbital_pullback τ σ equivτ equivσ a b

/-- C36: the image of the WHOLE root orbital is exactly one output orbital. -/
theorem root_orbital_image_exact (τ : A → Q) (σ : B → R)
    (equivτ : ∀ (g : G) x, τ (g • x) = g • τ x)
    (equivσ : ∀ (g : G) y, σ (g • y) = g • σ y)
    (a : A) (b : B) (q : Q) (r : R) :
    orbital (G := G) (τ a) (σ b) q r ↔
      ∃ x y, orbital (G := G) a b x y ∧ τ x = q ∧ σ y = r := by
  constructor
  · rintro ⟨g, hq, hr⟩
    exact ⟨g • a, g • b, ⟨g, rfl, rfl⟩,
      (equivτ g a).trans hq, (equivσ g b).trans hr⟩
  · rintro ⟨x, y, ⟨g, hx, hy⟩, hq, hr⟩
    exact ⟨g, (equivτ g a).symm.trans ((congrArg τ hx).trans hq),
      (equivσ g b).symm.trans ((congrArg σ hy).trans hr)⟩

/-- Diversity is imposed ONLY AFTER computing the full pullback/saturation. -/
def diversityPullback (τ : A → Q) (σ : B → R) (D : A → B → Prop)
    (Θ : Q → R → Prop) : A → B → Prop :=
  fun x y => pullback τ σ Θ x y ∧ D x y

/-- C37: exact final restriction for any actual root witness. -/
theorem diversity_saturation_of_witness (τ : A → Q) (σ : B → R)
    (equivτ : ∀ (g : G) x, τ (g • x) = g • τ x)
    (equivσ : ∀ (g : G) y, σ (g • y) = g • σ y)
    (D : A → B → Prop) {q : Q} {r : R} {a : A} {b : B}
    (witness : pullback τ σ (orbital (G := G) q r) a b) :
    diversityPullback τ σ D (orbital (G := G) q r) =
      (fun x y => saturation τ σ (orbital (G := G) a b) x y ∧ D x y) := by
  unfold diversityPullback
  rw [saturation_of_any_root_witness τ σ equivτ equivσ witness]

/-- C36/C37: restricted output pullbacks cover D and are equal on overlap.
Thus retaining only nonempty members is a partition of the actual D. -/
theorem diversity_pullbacks_partition (τ : A → Q) (σ : B → R)
    (D : A → B → Prop) :
    (∀ x y, D x y → ∃ q r,
      diversityPullback τ σ D (orbital (G := G) q r) x y) ∧
    (∀ q r q' r' x y,
      diversityPullback τ σ D (orbital (G := G) q r) x y →
      diversityPullback τ σ D (orbital (G := G) q' r') x y →
      diversityPullback τ σ D (orbital (G := G) q r) =
        diversityPullback τ σ D (orbital (G := G) q' r')) := by
  constructor
  · intro x y hD
    exact ⟨τ x, σ y, orbital_nonempty (τ x) (σ y), hD⟩
  · intro q r q' r' x y h h'
    unfold diversityPullback
    rw [output_orbital_pullbacks_partition_on_overlap τ σ q q' r r' x y h.1 h'.1]

/-- Every D-contained root orbital belongs wholly to exactly one partition part.
This is the induced partition of the set of actual diversity root orbitals. -/
theorem root_orbital_unique_diversity_part (τ : A → Q) (σ : B → R)
    (equivτ : ∀ (g : G) x, τ (g • x) = g • τ x)
    (equivσ : ∀ (g : G) y, σ (g • y) = g • σ y)
    (D : A → B → Prop) (a : A) (b : B)
    (inside : ∀ x y, orbital (G := G) a b x y → D x y) :
    (∀ x y, orbital (G := G) a b x y →
      diversityPullback τ σ D (orbital (G := G) (τ a) (σ b)) x y) ∧
    (∀ q r, (∃ x y, orbital (G := G) a b x y ∧
        diversityPullback τ σ D (orbital (G := G) q r) x y) →
      orbital (G := G) q r = orbital (G := G) (τ a) (σ b)) := by
  constructor
  · intro x y h
    exact ⟨root_orbital_has_unique_output_orbit τ σ equivτ equivσ a b x y h,
      inside x y h⟩
  · rintro q r ⟨x, y, hRoot, hOutput⟩
    exact orbital_eq_of_common_pair q (τ a) (τ x) r (σ b) (σ y) hOutput.1
      (root_orbital_has_unique_output_orbit τ σ equivτ equivσ a b x y hRoot)

end General

section SameRoot

variable {G A Q R : Type*} [Group G]
variable [MulAction G A] [MulAction G Q] [MulAction G R]

/-- C39/C40: one nonidentity kernel identification gives a distinct mate
in EVERY fibre, by the actual transitive original action. -/
theorem nonidentity_kernel_mate_everywhere (τ : A → Q)
    (equivariant : ∀ (g : G) x, τ (g • x) = g • τ x)
    (trans : ∀ x y : A, ∃ g : G, g • x = y)
    (nonidentity : ∃ u v : A, u ≠ v ∧ kernel τ u v) (a : A) :
    ∃ b : A, b ≠ a ∧ kernel τ b a := by
  obtain ⟨u, v, different, same⟩ := nonidentity
  obtain ⟨g, hg⟩ := trans u a
  refine ⟨g • v, ?_, ?_⟩
  · intro equal
    exact different (smul_left_cancel g (hg.trans equal.symm))
  · change τ (g • v) = τ a
    rw [equivariant, ← same, ← equivariant, hg]

/-- C38–C43 for arbitrary output representatives, including different Q and R.
The left side says the diversity pullback is empty; the right says both
surjections are bijective and the orbital is the same-root output graph. -/
theorem same_root_empty_diversity_iff (τ : A → Q) (σ : A → R)
    (ontoτ : Function.Surjective τ) (ontoσ : Function.Surjective σ)
    (equivτ : ∀ (g : G) x, τ (g • x) = g • τ x)
    (equivσ : ∀ (g : G) x, σ (g • x) = g • σ x)
    (trans : ∀ x y : A, ∃ g : G, g • x = y) (q : Q) (r : R) :
    (∀ x y, x ≠ y → ¬ pullback τ σ (orbital (G := G) q r) x y) ↔
      (Function.Bijective τ ∧ Function.Bijective σ ∧
        orbital (G := G) q r = (fun u v => ∃ x : A, u = τ x ∧ v = σ x)) := by
  obtain ⟨a, rfl⟩ := ontoτ q
  obtain ⟨b, rfl⟩ := ontoσ r
  rw [empty_diversity_pullback_iff τ σ equivτ equivσ trans a b]
  exact ⟨fun h => ⟨⟨h.1, ontoτ⟩, ⟨h.2.1, ontoσ⟩, h.2.2⟩,
    fun h => ⟨h.1.1, h.2.1.1, h.2.2⟩⟩

/-- C42: under the exact exception the FULL pullback is literally identity. -/
theorem graph_pullback_identity (τ : A → Q) (σ : A → R)
    (injectiveτ : Function.Injective τ) (injectiveσ : Function.Injective σ) :
    pullback τ σ (fun q r => ∃ x : A, q = τ x ∧ r = σ x) =
      (fun x y : A => x = y) := by
  funext x y
  apply propext
  constructor
  · rintro ⟨z, hx, hy⟩
    exact (injectiveτ hx).trans (injectiveσ hy).symm
  · rintro rfl
    exact ⟨x, rfl, rfl⟩

/-- C43: at most ONE output orbital can have empty real-diversity pullback. -/
theorem empty_diversity_orbital_unique (τ : A → Q) (σ : A → R)
    (ontoτ : Function.Surjective τ) (ontoσ : Function.Surjective σ)
    (equivτ : ∀ (g : G) x, τ (g • x) = g • τ x)
    (equivσ : ∀ (g : G) x, σ (g • x) = g • σ x)
    (trans : ∀ x y : A, ∃ g : G, g • x = y)
    {q q' : Q} {r r' : R}
    (empty₁ : ∀ x y, x ≠ y → ¬ pullback τ σ (orbital (G := G) q r) x y)
    (empty₂ : ∀ x y, x ≠ y → ¬ pullback τ σ (orbital (G := G) q' r') x y) :
    orbital (G := G) q r = orbital (G := G) q' r' := by
  have h₁ := (same_root_empty_diversity_iff τ σ ontoτ ontoσ equivτ equivσ trans q r).mp empty₁
  have h₂ := (same_root_empty_diversity_iff τ σ ontoτ ontoσ equivτ equivσ trans q' r').mp empty₂
  exact h₁.2.2.trans h₂.2.2.symm

end SameRoot

section TypedRoots

variable {ι : Type*} {X : ι → Type*} {G : Type*} [Group G]
variable [∀ i, MulAction G (X i)]

/-- The diversity convention uses actual tagged root points, not output equality. -/
def typedRootDiversity {i j : ι} (x : X i) (y : X j) : Prop :=
  (⟨i, x⟩ : Sigma X) ≠ ⟨j, y⟩

/-- C38: for disjoint original sorts EVERY output orbital has real diversity. -/
theorem disjoint_roots_diversity_nonempty {i j : ι} (different : i ≠ j)
    {Q R : Type*} [MulAction G Q] [MulAction G R]
    (τ : X i → Q) (σ : X j → R)
    (ontoτ : Function.Surjective τ) (ontoσ : Function.Surjective σ)
    (q : Q) (r : R) :
    ∃ x y, diversityPullback τ σ typedRootDiversity (orbital (G := G) q r) x y := by
  obtain ⟨x, y, h⟩ := output_orbital_has_root_witness (G := G) τ σ ontoτ ontoσ q r
  exact ⟨x, y, h, cross_sort_real_points_distinct different x y⟩

/-- C38: an empty diversity part forces equality of the original sort indices. -/
theorem empty_typed_diversity_forces_same_sort {i j : ι}
    {Q R : Type*} [MulAction G Q] [MulAction G R]
    (τ : X i → Q) (σ : X j → R)
    (ontoτ : Function.Surjective τ) (ontoσ : Function.Surjective σ)
    (q : Q) (r : R)
    (empty : ∀ x y,
      ¬ diversityPullback τ σ typedRootDiversity (orbital (G := G) q r) x y) : i = j := by
  by_contra different
  obtain ⟨x, y, h⟩ := disjoint_roots_diversity_nonempty (G := G) different τ σ ontoτ ontoσ q r
  exact empty x y h

end TypedRoots
end CCO.QuotientTransport.SharedActions
