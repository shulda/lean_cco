import CCO.SIR.Negative.FiniteGlobal

/-!
# Actual finite quotient consumers

These corollaries take maps on original real points. A finite target is
construction data, never an expansion naming its fibres. Constancy of
the map is the properness boundary; the identity map recovers the finite
nontrivial real-carrier boundary.
-/

universe u v w

namespace CCO.SIR.Negative

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource ι X) (i : ι)
variable {G : Type*} [Group G] [∀ j : ι, MulAction G (X j)]

/-- Any nonconstant finite-valued map with invariant kernel obstructs a
real SIR, using precisely the explicit full relative Hasse provider. The
map need not be named in the old language or onto its displayed target. -/
theorem finite_quotient_map_obstruction_of_provider
    (H : HomogeneousSource S G) (P : FullRelativeHasseProvider S i)
    {Q : Type*} [Finite Q] (π : X i → Q)
    (hInv : ∀ (g : G) x y, π x = π y → π (g • x) = π (g • y))
    (x y : X i) (hne : π x ≠ π y)
    (I : Finset (X i) → Finset (X i) → Finset (X i) → Prop) :
    ¬ EmptyBaseSingletonAxioms (G := G) I := by
  let E : Setoid (X i) := Setoid.ker π
  letI : Finite (Quotient E) :=
    Finite.of_equiv (Set.range π) (Setoid.quotientKerEquivRange π).symm
  have hproper : E < ⊤ := by
    apply lt_of_le_of_ne le_top
    intro heq
    have hxy : E x y := by rw [heq]; trivial
    exact hne hxy
  exact original_finite_global_obstruction_of_provider S i H P E hInv hproper I

/-- Identity-kernel boundary: a finite source with two distinct real
points cannot have even the singleton SIR reduct, under full Hasse. -/
theorem finite_real_carrier_obstruction_of_provider
    (H : HomogeneousSource S G) (P : FullRelativeHasseProvider S i)
    [Finite (X i)] (x y : X i) (hne : x ≠ y)
    (I : Finset (X i) → Finset (X i) → Finset (X i) → Prop) :
    ¬ EmptyBaseSingletonAxioms (G := G) I := by
  apply finite_quotient_map_obstruction_of_provider S i H P id
    (fun g _ _ h => congrArg (fun z : X i => g • z) h) x y hne I

end CCO.SIR.Negative
