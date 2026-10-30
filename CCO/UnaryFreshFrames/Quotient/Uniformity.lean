import CCO.UnaryFreshFrames.Quotient.Fibres

/-! Uniformity of the ACTUAL relative fibre index follows from transitivity,
without commuting kernels, distributivity, or formal cardinal division. -/
universe u v w z
namespace CCO.UnaryFreshFrames.Quotient
variable {G : Type u} [Group G] {M : Type v} {Q : Type w} {V : Type z}
variable [MulAction G M] [MulAction G Q] [MulAction G V]

theorem smul_mem_fibreValues (p : M → Q) (hp : Equivariant (G := G) p)
    (f : M → V) (hf : Equivariant (G := G) f) (g : G) {b : Q} {y : V}
    (hy : y ∈ FibreValues p f b) : g • y ∈ FibreValues p f (g • b) := by
  rcases hy with ⟨x, hx, rfl⟩
  refine ⟨g • x, ?_, hf g x⟩
  exact (hp g x).trans (congrArg (fun b => g • b) hx)

/-- The actual motion restricts to a bijection between the two fibre images. -/
def fibreValuesEquiv (p : M → Q) (hp : Equivariant (G := G) p)
    (f : M → V) (hf : Equivariant (G := G) f) (g : G) (b : Q) :
    FibreValues p f b ≃ FibreValues p f (g • b) where
  toFun y := ⟨g • y.val, smul_mem_fibreValues p hp f hf g y.property⟩
  invFun y := ⟨g⁻¹ • y.val, by
    have h := smul_mem_fibreValues p hp f hf g⁻¹ y.property
    simpa only [inv_smul_smul] using h⟩
  left_inv _ := Subtype.ext (inv_smul_smul _ _)
  right_inv _ := Subtype.ext (smul_inv_smul _ _)

/-- C21: any two ACTUAL quotient fibres have the same relative-image cardinal.
This explicit equivalence covers finite AND infinite indices. -/
noncomputable def arbitraryFibreValuesEquiv (ht : Transitive (G := G) (M := M))
    (p : M → Q) (hp : Equivariant (G := G) p) (hps : Function.Surjective p)
    (f : M → V) (hf : Equivariant (G := G) f) (b c : Q) :
    FibreValues p f b ≃ FibreValues p f c := by
  apply Classical.choice
  obtain ⟨x, hx⟩ := hps b
  obtain ⟨y, hy⟩ := hps c
  obtain ⟨g, hg⟩ := ht x y
  have he : g • b = c := by rw [← hx, ← hp g x, hg, hy]
  exact ⟨(fibreValuesEquiv p hp f hf g b).trans (Set.equivOfEq (by rw [he]))⟩

end CCO.UnaryFreshFrames.Quotient
