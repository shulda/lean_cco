import CCO.GroupActions
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.Algebra.Group.TypeTags.Finite

/-! B040 C27–C32: consumers of the existing shared B001 point-lifting API.
The output is a prescribed group element, including elements acting trivially.
No existing receiving export or consumer is moved to this package. -/

namespace CCO.QuotientTransport.SharedActions

section General

variable {K Γ Y B : Type*} [Group K] [Group Γ]
variable [MulAction K Y] [MulAction Γ B]

/-- C27: an arbitrary group lift puts the point in the requested actual fibre. -/
theorem lifted_point_same_fibre (ρ : K →* Γ) (π : Y → B)
    (equivariant : ∀ k x, π (k • x) = ρ k • π x)
    {x y : Y} {γ : Γ} (compatible : γ • π x = π y)
    {k₀ : K} (image : ρ k₀ = γ) : π (k₀ • x) = π y := by
  rw [equivariant, image, compatible]

/-- C28: the correcting kernel element multiplies on the LEFT. -/
theorem left_kernel_correction (ρ : K →* Γ) {x y : Y} {γ : Γ}
    {k₀ h : K} (image : ρ k₀ = γ) (kernel : ρ h = 1)
    (correct : h • (k₀ • x) = y) :
    ρ (h * k₀) = γ ∧ (h * k₀) • x = y := by
  constructor
  · simp only [map_mul, kernel, image, one_mul]
  · simpa only [mul_smul] using correct

/-- C29: nonempty domain and onto point map force onto GROUP map. -/
theorem onto_of_all_requests [Nonempty Y] (ρ : K →* Γ) (π : Y → B)
    (onto : Function.Surjective π) (requests : GroupActions.PrescribedLift ρ π) :
    Function.Surjective ρ := by
  intro γ
  obtain ⟨x⟩ := ‹Nonempty Y›
  obtain ⟨y, hy⟩ := onto (γ • π x)
  obtain ⟨k, hk, _⟩ := requests x y γ hy.symm
  exact ⟨k, hk⟩

/-- C30: the literal request γ=1 gives actual kernel transitivity. -/
theorem kernel_transitive_of_all_requests (ρ : K →* Γ) (π : Y → B)
    (requests : GroupActions.PrescribedLift ρ π) : GroupActions.FibreTransitive ρ π := by
  intro x y same
  exact requests x y 1 (by simpa only [one_smul] using same)

/-- C31: the original shared B001 theorem, applied without extra hypotheses. -/
theorem shared_point_lifting_consumer [Nonempty Y] (ρ : K →* Γ) (π : Y → B)
    (onto : Function.Surjective π)
    (equivariant : ∀ k x, π (k • x) = ρ k • π x) :
    (Function.Surjective ρ ∧ GroupActions.FibreTransitive ρ π) ↔
      GroupActions.PrescribedLift ρ π :=
  GroupActions.prescribed_action_point_lifting ρ π onto equivariant

end General

namespace NonfaithfulNonsplit

abbrev C4 := Multiplicative (ZMod 4)
abbrev C2 := Multiplicative (ZMod 2)

def reduction : ZMod 4 →+ ZMod 2 :=
  (ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2)).toAddMonoidHom

def rho : C4 →* C2 := reduction.toMultiplicative

theorem rho_surjective : Function.Surjective rho := by
  intro b
  obtain ⟨a, ha⟩ := ZMod.castHom_surjective (by decide : 2 ∣ 4) b.toAdd
  exact ⟨Multiplicative.ofAdd a, congrArg Multiplicative.ofAdd ha⟩

def nontrivial : C2 := Multiplicative.ofAdd 1

theorem nontrivial_sq : nontrivial * nontrivial = 1 := by decide
theorem nontrivial_ne_one : nontrivial ≠ 1 := by decide

theorem order_two_image : ∀ x : C4, x * x = 1 → rho x = 1 := by decide

/-- A section would send the C2 generator to an impossible odd element of order ≤2. -/
theorem no_homomorphic_section :
    ¬ ∃ s : C2 →* C4, rho.comp s = MonoidHom.id C2 := by
  rintro ⟨s, split_eq⟩
  have square : s nontrivial * s nontrivial = 1 := by
    rw [← map_mul, nontrivial_sq, map_one]
  have zero := order_two_image (s nontrivial) square
  have image : rho (s nontrivial) = nontrivial :=
    congrArg (fun f : C2 →* C2 => f nontrivial) split_eq
  exact nontrivial_ne_one (image.symm.trans zero)

/-- C4 acts on the TWO-point target through reduction, rather than regularly. -/
local instance : MulAction C4 C2 where
  smul k x := rho k * x
  one_smul x := by change rho 1 * x = x; rw [map_one, one_mul]
  mul_smul k h x := by
    change rho (k * h) * x = rho k * (rho h * x)
    rw [map_mul, mul_assoc]

theorem projection_equivariant (k : C4) (x : C2) :
    (id : C2 → C2) (k • x) = rho k • (id : C2 → C2) x := rfl

/-- Exact C32 source example: Y=B=C2 and π=id, so every fibre is a singleton. -/
theorem requests_on_two_points : GroupActions.PrescribedLift rho (id : C2 → C2) := by
  intro x y γ compatible
  change γ * x = y at compatible
  obtain ⟨k, hk⟩ := rho_surjective γ
  exact ⟨k, hk, by change rho k * x = y; simpa only [hk] using compatible⟩

theorem onto_and_singleton_fibres :
    Function.Surjective rho ∧ GroupActions.FibreTransitive rho (id : C2 → C2) :=
  (GroupActions.prescribed_action_point_lifting rho id (fun x => ⟨x, rfl⟩)
    projection_equivariant).mpr requests_on_two_points

def invisible : C4 := Multiplicative.ofAdd 2

theorem invisible_nonidentity : invisible ≠ 1 := by decide
theorem invisible_image : rho invisible = 1 := by decide
theorem invisible_fixes_every_point (x : C2) : invisible • x = x := by
  change rho invisible * x = x
  rw [invisible_image, one_mul]

/-- The action is genuinely nonfaithful and the epimorphism genuinely nonsplit. -/
theorem nonfaithful_nonsplit_requests :
    GroupActions.PrescribedLift rho (id : C2 → C2) ∧
    (∃ k : C4, k ≠ 1 ∧ ∀ x : C2, k • x = x) ∧
    ¬ (∃ s : C2 →* C4, rho.comp s = MonoidHom.id C2) :=
  ⟨requests_on_two_points, ⟨invisible, invisible_nonidentity,
    invisible_fixes_every_point⟩, no_homomorphic_section⟩

end NonfaithfulNonsplit
end CCO.QuotientTransport.SharedActions
