import CCO.FiniteKernel.FiniteTests
import CCO.FiniteKernel.LinearDual
import CCO.FiniteKernel.FiniteAnnihilator
import Mathlib.Algebra.Module.Submodule.Map
import Mathlib.Data.Fintype.Pi

/-!
# Actual finite projection annihilators and width two

R is spanned globally BEFORE restricting supports. The marginal rows are the
true intersections R∩D_T, for every T⊆S of size at most two, including SINGLETONS.
No original local H_CD is substituted for an actual marginal. The conclusion
is only the displayed equality of an actual finite projection with its own
marginal constraint group, not an arbitrary elimination theorem.
-/

universe u v w
namespace CCO.FiniteKernel
noncomputable section
variable (K : Type u) [Field K] {I : Type v} (V : I → Type w) [DecidableEq I]
variable [∀ i,AddCommGroup (V i)] [∀ i,Module K (V i)]

def finiteProjection (N : Submodule K (∀ i,V i)) (A : Finset I) :
    Submodule K (FiniteProduct V A) := N.map (restrictVec K V A)

def marginalRows (R : Submodule K (TestSpace K V)) (A : Finset I) :
    Submodule K (TestSpace K V) :=
  ⨆ (T : Finset I) (_hTA : T ⊆ A) (_hc : T.card ≤ 2), R ⊓ restrictedTestSpace K V T

def marginalSpace (N : Submodule K (∀ i,V i)) (A : Finset I) :
    Submodule K (FiniteProduct V A) :=
  ⨅ (T : Finset I) (hTA : T ⊆ A) (_hc : T.card ≤ 2),
    (finiteProjection K V N T).comap (restrictBetween K V hTA)

@[simp] theorem mem_marginalSpace (N : Submodule K (∀ i,V i)) (A : Finset I)
    (x : FiniteProduct V A) : x ∈ marginalSpace K V N A ↔
      ∀ (T : Finset I) (hTA : T ⊆ A), T.card ≤ 2 →
        restrictBetween K V hTA x ∈ finiteProjection K V N T := by
  simp only [marginalSpace,Submodule.mem_iInf,Submodule.mem_comap]

theorem projection_le_marginalSpace (N : Submodule K (∀ i,V i)) (A : Finset I) :
    finiteProjection K V N A ≤ marginalSpace K V N A := by
  intro z hz
  obtain ⟨x,hx,rfl⟩ := hz
  apply (mem_marginalSpace K V N A _).mpr
  intro T hTA _
  exact ⟨x,hx,(restrictBetween_restrictVec K V hTA x).symm⟩

theorem marginalSpace_small (N : Submodule K (∀ i,V i)) (A : Finset I) (hc : A.card ≤ 2) :
    marginalSpace K V N A = finiteProjection K V N A := by
  apply le_antisymm _ (projection_le_marginalSpace K V N A)
  intro z hz
  have hh := (mem_marginalSpace K V N A z).mp hz A (Finset.Subset.refl A) hc
  change z ∈ finiteProjection K V N A at hh
  exact hh

theorem marginalRows_le (R : Submodule K (TestSpace K V)) (A : Finset I) :
    marginalRows K V R A ≤ restrictedTestSpace K V A := by
  refine iSup_le fun T => iSup_le fun hTA => iSup_le fun _ => ?_
  exact inf_le_right.trans (restrictedTestSpace_mono K V hTA)

theorem marginalRows_contains (R : Submodule K (TestSpace K V))
    {T A : Finset I} (hTA : T ⊆ A) (hc : T.card ≤ 2) :
    R ⊓ restrictedTestSpace K V T ≤ marginalRows K V R A :=
  le_iSup_of_le T (le_iSup_of_le hTA (le_iSup_of_le hc le_rfl))

theorem finiteProduct_countable [∀ i,Finite (V i)] (A : Finset I) :
    Countable (FiniteProduct V A) := by
  classical
  letI : ∀ i : ↥A,Fintype (V i.val) := fun _ => Fintype.ofFinite _
  infer_instance

variable [∀ i,FiniteDimensional K (V i)] [Countable (TestSpace K V)]

/-- C13 in finite coordinate duals. -/
theorem restricted_annihilator (R : Submodule K (TestSpace K V)) (A : Finset I) :
    (finiteProjection K V (perp K V R) A).dualAnnihilator =
      R.comap (extendForm K V A) := by
  ext phi
  constructor
  · intro hphi
    apply (ann_perp K V R).le
    apply (mem_ann K V _ _).mpr
    intro x hx
    rw [eval_extendForm]
    exact (Submodule.mem_dualAnnihilator phi).mp hphi _ ⟨x,hx,rfl⟩
  · intro hphi
    apply (Submodule.mem_dualAnnihilator phi).mpr
    intro z hz
    obtain ⟨x,hx,rfl⟩ := hz
    have hz := (mem_perp K V R x).mp hx _ hphi
    rwa [eval_extendForm] at hz

/-- C13 literally as R∩D_S, identifying finite forms with their injective
zero-extensions into the actual finite-support test space. -/
theorem restricted_annihilator_map (R : Submodule K (TestSpace K V)) (A : Finset I) :
    (finiteProjection K V (perp K V R) A).dualAnnihilator.map (extendForm K V A) =
      R ⊓ restrictedTestSpace K V A := by
  rw [restricted_annihilator,Submodule.map_comap_eq]
  exact inf_comm ((extendForm K V A).range) R

variable [∀ i,Finite (V i)]

theorem marginalSpace_eq_projection_perp (R : Submodule K (TestSpace K V)) (A : Finset I) :
    marginalSpace K V (perp K V R) A =
      finiteProjection K V (perp K V (marginalRows K V R A)) A := by
  ext z
  constructor
  · intro hz
    let x := extendVec K V A z
    have hx : x ∈ perp K V (marginalRows K V R A) := by
      apply (mem_perp K V _ x).mpr
      have hle : marginalRows K V R A ≤ (evalTuple K V x).ker := by
        refine iSup_le fun T => iSup_le fun hTA => iSup_le fun hc => ?_
        intro ell hell
        have hD : ell ∈ (extendForm K V T).range := hell.2
        obtain ⟨phi,rfl⟩ := hD
        have hphi : phi ∈ (finiteProjection K V (perp K V R) T).dualAnnihilator := by
          rw [restricted_annihilator]
          exact hell.1
        change evalTuple K V x (extendForm K V T phi) = 0
        rw [eval_extendForm]
        have hrestr : restrictVec K V T x = restrictBetween K V hTA z := by
          simpa only [x,restrict_extendVec] using
            (restrictBetween_restrictVec K V hTA (extendVec K V A z)).symm
        rw [hrestr]
        exact (Submodule.mem_dualAnnihilator phi).mp hphi _
          ((mem_marginalSpace K V _ A z).mp hz T hTA hc)
      exact fun ell hell => hle hell
    exact ⟨x,hx,restrict_extendVec K V A z⟩
  · intro hz
    obtain ⟨x,hx,rfl⟩ := hz
    apply (mem_marginalSpace K V _ A _).mpr
    intro T hTA hc
    letI : Countable (FiniteProduct V T) := finiteProduct_countable V T
    apply (mem_iff_annihilator_tests K _ _).mpr
    intro phi hphi
    have hR : extendForm K V T phi ∈ R := by
      rw [restricted_annihilator] at hphi
      exact hphi
    have hW : extendForm K V T phi ∈ marginalRows K V R A :=
      marginalRows_contains K V R hTA hc ⟨hR,⟨phi,rfl⟩⟩
    have hz := (mem_perp K V _ x).mp hx _ hW
    rw [eval_extendForm] at hz
    simpa only [restrictBetween_restrictVec] using hz

/-- C14: the annihilator of the ACTUAL singleton/pair-marginal constraint
space is exactly the span of TRUE restricted marginal rows. -/
theorem marginal_annihilator_map (R : Submodule K (TestSpace K V)) (A : Finset I) :
    (marginalSpace K V (perp K V R) A).dualAnnihilator.map (extendForm K V A) =
      marginalRows K V R A := by
  rw [marginalSpace_eq_projection_perp,restricted_annihilator_map]
  exact inf_eq_left.mpr (marginalRows_le K V R A)

/-- C15 exact width-two criterion. Its left side is only the displayed
ACTUAL finite image and its own marginal constraints. -/
theorem width_two_iff (R : Submodule K (TestSpace K V)) (A : Finset I) :
    finiteProjection K V (perp K V R) A = marginalSpace K V (perp K V R) A ↔
      R ⊓ restrictedTestSpace K V A = marginalRows K V R A := by
  letI : Countable (FiniteProduct V A) := finiteProduct_countable V A
  constructor
  · intro h
    have hh := congrArg (fun U : Submodule K (FiniteProduct V A) =>
      U.dualAnnihilator.map (extendForm K V A)) h
    simpa only [restricted_annihilator_map,marginal_annihilator_map] using hh
  · intro h
    apply annihilator_injective K
    apply Submodule.map_injective_of_injective (extendForm_injective K V A)
    rw [restricted_annihilator_map,marginal_annihilator_map]
    exact h

end
end CCO.FiniteKernel
