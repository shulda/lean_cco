import CCO.GuardedTwoRoot.G1HiddenModel
import CCO.UnaryFreshFrames.SAPAvoidance

/-! Source14 C42: hereditary SAP for the ACTUAL coarse block expansion
over EVERY finite closed hidden base, including orphan quotient vertices.
Real clones move with every owner block fixed; an unanchored quotient
block moves by swaps avoiding all owners in the closed base. -/

namespace CCO.GuardedTwoRoot.G1.Hidden
open CCO.UnaryFreshFrames
noncomputable section

def blockFixedAut (g : G1.Aut) (hBlock : ∀ x, block (g • x) = block x) : model.Aut := by
  have hBlock' : ∀ x, block (g.val x) = block x := hBlock
  have hColour' : ∀ x y, colour (g.val x) (g.val y) = colour x y := g.property
  refine ⟨Equiv.sumCongr g.val (Equiv.refl ℕ),?_,?_,?_⟩
  · rintro (x | q) <;> rfl
  · rintro F (x | q)
    · exact congrArg Sum.inr (hBlock x).symm
    · rfl
  · intro R xs
    change (sort (Equiv.sumCongr g.val (Equiv.refl ℕ) (xs 0)) = leftSort R ∧
      sort (Equiv.sumCongr g.val (Equiv.refl ℕ) (xs 1)) = rightSort R ∧
      relationData R (Equiv.sumCongr g.val (Equiv.refl ℕ) (xs 0))
        (Equiv.sumCongr g.val (Equiv.refl ℕ) (xs 1))) ↔
      (sort (xs 0) = leftSort R ∧ sort (xs 1) = rightSort R ∧
        relationData R (xs 0) (xs 1))
    cases R with
    | inl atom =>
      cases hx : xs 0 <;> cases hy : xs 1
      all_goals simp [leftSort,rightSort,sort,relationData,realValue,hColour']
    | inr name =>
      cases name <;> cases hx : xs 0 <;> cases hy : xs 1
      all_goals simp [leftSort,rightSort,sort,relationData,owner,hBlock']

theorem real_orbit_infinite (D : Set Point) (hD : D.Finite)
    (x : Real) (hx : (.inl x : Point) ∉ D) :
    (orbitOver model.Aut D (.inl x)).Infinite := by
  let oldD : Set Real := Sum.inl ⁻¹' D
  have hOldD : oldD.Finite := hD.preimage Sum.inl_injective.injOn
  obtain ⟨image,motion,hInj,hMove,hFix,hBlock⟩ :=
    G1.infinite_clone_family oldD hOldD x hx
  apply Set.infinite_of_injective_forall_mem (f := fun n => (Sum.inl (image n) : Point))
  · intro n m he
    exact hInj (Sum.inl.inj he)
  · intro n
    apply (mem_orbitOver_iff model.Aut).mpr
    refine ⟨blockFixedAut (motion n) (hBlock n),?_,?_⟩
    · rintro (y | q) hy
      · exact congrArg Sum.inl (hFix n y hy)
      · rfl
    · exact congrArg Sum.inl (hMove n)

def blockSwap (q t : ℕ) : model.Aut :=
  wreathAut (Equiv.swap q t) (fun _ => Equiv.refl Bool) (fun _ => Equiv.refl ℕ)

theorem blockSwap_fixed (q t : ℕ) (x : Point)
    (hq : owner x ≠ q) (ht : owner x ≠ t) : blockSwap q t • x = x := by
  cases x with
  | inl x =>
    apply congrArg Sum.inl
    apply G1.real_ext
    · exact Equiv.swap_apply_of_ne_of_ne hq ht
    · rfl
    · rfl
  | inr b => exact congrArg Sum.inr (Equiv.swap_apply_of_ne_of_ne hq ht)

theorem quotient_orbit_infinite (D : Set Point) (hD : D.Finite)
    (hClosed : model.Closed D) (q : ℕ) (hq : (.inr q : Point) ∉ D) :
    (orbitOver model.Aut D (.inr q)).Infinite := by
  classical
  let owners := (hD.image owner).toFinset
  let bound := owners.sup id
  let target (n : ℕ) := bound + 1 + n
  have hNotQ (x : Point) (hx : x ∈ D) : owner x ≠ q := by
    intro he
    have hp := hClosed () x hx
    change (Sum.inr (owner x) : Point) ∈ D at hp
    rw [he] at hp
    exact hq hp
  have hNotTarget (n : ℕ) (x : Point) (hx : x ∈ D) : owner x ≠ target n := by
    have hle : owner x ≤ bound :=
      Finset.le_sup (s := owners) (f := id) (b := owner x)
        ((hD.image owner).mem_toFinset.mpr ⟨x,hx,rfl⟩)
    dsimp only [target]
    omega
  apply Set.infinite_of_injective_forall_mem (f := fun n => (Sum.inr (target n) : Point))
  · intro n m he
    have hh := Sum.inr.inj he
    dsimp only [target] at hh
    omega
  · intro n
    apply (mem_orbitOver_iff model.Aut).mpr
    refine ⟨blockSwap q (target n),?_,?_⟩
    · intro x hx
      exact blockSwap_fixed q (target n) x (hNotQ x hx) (hNotTarget n x hx)
    · change (Sum.inr (Equiv.swap q (target n) q) : Point) = .inr (target n)
      simp

/-- Actual infinite full-automorphism orbits over EVERY finite CLOSED
base; no terminal index exclusion or supplied orbit provider is used. -/
theorem infinite_closed_orbits : model.InfiniteClosedOrbits model.Aut := by
  intro D hD hClosed x hx
  cases x with
  | inl x => exact real_orbit_infinite D hD x hx
  | inr q => exact quotient_orbit_infinite D hD hClosed q hx

theorem locallyFinite : model.LocallyFinite := by
  intro D hD
  apply (hD.union (hD.image projection)).subset
  apply model.closure_minimal ?_ (fun _ hx => Or.inl hx)
  rintro F x (hx | ⟨y,hy,rfl⟩)
  · exact Or.inr ⟨x,hx,rfl⟩
  · exact Or.inr ⟨y,hy,rfl⟩

/-- The genuine p/q/r coarse quotient expansion has hereditary hidden
SAP, despite the original finite index-two bit cut. -/
theorem ageSAP : model.AgeSAP :=
  model.ageSAP_of_infiniteClosedOrbits homogeneous infinite_closed_orbits

/-- All scope conditions of this actual hidden counterexample are
proved, rather than being finite-window diagnostics. -/
theorem actual_scope : Countable Point ∧ Finite language.Sorts ∧
    Finite language.Func ∧ Finite language.Rel ∧ model.LocallyFinite ∧
    model.Homogeneous ∧ model.AgeSAP :=
  ⟨inferInstance,inferInstance,inferInstance,inferInstance,locallyFinite,homogeneous,ageSAP⟩

end
end CCO.GuardedTwoRoot.G1.Hidden
