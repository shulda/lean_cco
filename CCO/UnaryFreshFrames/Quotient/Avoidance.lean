import CCO.UnaryFreshFrames.Quotient.Fibres

/-! One common quotient-fibre motion avoids ALL unforced semantic terms. -/
universe u v w z
namespace CCO.UnaryFreshFrames.Quotient
variable {G : Type u} [Group G] {M : Type v} {Q : Type w} {V : Type z}
variable [MulAction G M] [MulAction G Q] [MulAction G V]

/-- The finite set of distinct values, not a finite list of syntactic terms. -/
def UnforcedValues (p : M → Q) (T : Set (M → V)) (x : M) : Set V :=
  {y | ∃ f ∈ T, ¬ KernelLe p f ∧ f x = y}

/-- C22–C23: the action on the ACTUAL quotient fibre produces ONE common
representative, simultaneously for every unforced semantic term function.
No homogeneity, SAP, finite language or real-base orbit hypothesis is used. -/
theorem common_fibre_avoidance (ht : Transitive (G := G) (M := M)) (p : M → Q)
    (hp : Equivariant (G := G) p) (T : Set (M → V))
    (hT : ∀ f ∈ T, Equivariant (G := G) f) (x₀ : M)
    (hfinite : ((fun f : M → V => f x₀) '' T).Finite)
    (hinfinite : ∀ f ∈ T, ¬ KernelLe p f → (FibreValues p f (p x₀)).Infinite)
    (Z : Finset V) :
    ∃ x : M, p x = p x₀ ∧ ∀ f ∈ T, ¬ KernelLe p f → f x ∉ Z := by
  classical
  have hs : (UnforcedValues p T x₀).Finite := hfinite.subset (by
    rintro y ⟨f, hf, _, rfl⟩
    exact ⟨f, hf, rfl⟩)
  let S := hs.toFinset
  have horbit (y : V) (hy : y ∈ S) :
      (MulAction.orbit (MulAction.stabilizer G (p x₀)) y).Infinite := by
    obtain ⟨f, hf, hn, rfl⟩ := hs.mem_toFinset.mp hy
    rw [orbit_eq_fibreValues ht p hp f (hT f hf) x₀]
    exact hinfinite f hf hn
  obtain ⟨g, hg⟩ := CCO.AclOwners.finite_action_avoidance
    (G := MulAction.stabilizer G (p x₀)) S Z horbit
  refine ⟨g • x₀, ?_, ?_⟩
  · change p ((g : G) • x₀) = p x₀
    rw [hp]
    exact g.property
  · intro f hf hn hz
    have hmem : f x₀ ∈ S := hs.mem_toFinset.mpr ⟨f, hf, hn, rfl⟩
    have hne := hg (f x₀) hmem (f (g • x₀)) hz
    exact hne (hT f hf g x₀).symm

/-- Forced values remain literal, even when included in the forbidden set. -/
theorem forced_value_retained {p : M → Q} {f : M → V} (hforced : KernelLe p f)
    {x y : M} (hxy : p x = p y) : f x = f y := hforced x y hxy

/-- The identity real map is unforced as soon as the actual projection kernel
is strictly above equality. Thus the SAME common choice avoids the forbidden
set as a real vertex, not merely through its nonidentity term values. -/
theorem identity_unforced (p : M → Q) (embedding : M → V)
    (hi : Function.Injective embedding) (hn : ¬ Function.Injective p) :
    ¬ KernelLe p embedding := by
  intro h
  apply hn
  intro x y hxy
  exact hi (h x y hxy)

end CCO.UnaryFreshFrames.Quotient
