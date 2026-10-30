import CCO.UnaryFreshFrames.Quotient.Fibres

/-! The two local necessity mechanisms, before invoking SAP. These lemmas
can be used for the FULL automorphism action even when a smaller subgroup
supplies the transitivity and a moving witness. -/
universe u v w z
namespace CCO.UnaryFreshFrames.Quotient
variable {G : Type u} [Group G] {M : Type v} {Q : Type w} {V : Type z}
variable [MulAction G M] [MulAction G Q] [MulAction G V]

/-- C38: a forced value is fixed over its quotient point without assuming a
named factor. This applies to every full automorphism fixing that point. -/
theorem forced_value_fixed (p : M → Q) (hp : Equivariant (G := G) p)
    (f : M → V) (hf : Equivariant (G := G) f) (hk : KernelLe p f) (x : M)
    (g : G) (hgb : g • p x = p x) : g • f x = f x := by
  rw [← hf g x]
  apply hk
  exact (hp g x).trans hgb

/-- Full stabilizer orbits always lie in the actual fibre image. There is
NO full-group transitivity hypothesis in this assertion. -/
theorem orbit_subset_fibreValues (p : M → Q) (hp : Equivariant (G := G) p)
    (f : M → V) (hf : Equivariant (G := G) f) (x : M) :
    MulAction.orbit (MulAction.stabilizer G (p x)) (f x) ⊆ FibreValues p f (p x) := by
  rintro y ⟨g, rfl⟩
  refine ⟨(g : G) • x, ?_, hf g x⟩
  change p ((g : G) • x) = p x
  exact (hp g x).trans g.property

/-- C42: a finite actual fibre image gives algebraicity for the FULL action,
even if the transitive group used elsewhere is a proper subgroup. -/
theorem finite_orbit_of_finite_fibreValues (p : M → Q) (hp : Equivariant (G := G) p)
    (f : M → V) (hf : Equivariant (G := G) f) (x : M)
    (hfin : (FibreValues p f (p x)).Finite) :
    (MulAction.orbit (MulAction.stabilizer G (p x)) (f x)).Finite :=
  hfin.subset (orbit_subset_fibreValues p hp f hf x)

/-- A base-fixing element fixes every equivariant named value of the base. -/
theorem equivariant_base_value_fixed (s : Q → V) (hs : Equivariant (G := G) s)
    (b : Q) (g : G) (hgb : g • b = b) : g • s b = s b := by
  rw [← hs g b, hgb]

/-- C43: any actual subgroup motion over b rules out EVERY named equivariant
term value over b. No identification of subgroup and full-group orbits occurs. -/
theorem moved_not_base_value (s : Q → V) (hs : Equivariant (G := G) s)
    (b : Q) (v : V) (g : G) (hgb : g • b = b) (hmove : g • v ≠ v) : v ≠ s b := by
  intro he
  apply hmove
  rw [he]
  exact equivariant_base_value_fixed s hs b g hgb

/-- C47: missing named factorisation gives a local off-named-closure value.
The family N will be instantiated by actual named well-sorted terms. -/
theorem no_factor_not_named_value (ht : Transitive (G := G) (M := M))
    (p : M → Q) (hp : Equivariant (G := G) p)
    (f : M → V) (hf : Equivariant (G := G) f)
    (N : Set (Q → V)) (hN : ∀ s ∈ N, Equivariant (G := G) s)
    (hn : ¬ ∃ s ∈ N, f = s ∘ p) (x : M) :
    f x ∉ (fun s : Q → V => s (p x)) '' N := by
  rintro ⟨s, hs, he⟩
  exact hn ⟨s, hs, factor_of_one_value ht p hp f hf s (hN s hs) x he.symm⟩

end CCO.UnaryFreshFrames.Quotient
