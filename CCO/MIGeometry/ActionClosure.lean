import CCO.AclOwners.AclCore

/-! Absolute real closure commutes with actual group motions. -/
universe v t
namespace CCO.MIGeometry
open RealClosure.Bounds AclOwners
variable {M : Type v} {G : Type t} [Group G] [MulAction G M] [DecidableEq M]

theorem orbitOver_image_smul (g : G) (A : Finset M) (x : M) :
    orbitOver G (A.image (fun a => g • a)) (g • x) =
      (fun y => g • y) '' orbitOver G A x := by
  ext y
  constructor
  · rintro ⟨h,hh,rfl⟩
    refine ⟨(g⁻¹ * h * g) • x,⟨g⁻¹ * h * g,?_,rfl⟩,?_⟩
    · intro a ha
      rw [mul_smul,mul_smul,hh _ (Finset.mem_image.mpr ⟨a,ha,rfl⟩),inv_smul_smul]
    · simp only [mul_smul,smul_inv_smul]
  · rintro ⟨y,⟨h,hh,rfl⟩,rfl⟩
    refine ⟨g * h * g⁻¹,?_,?_⟩
    · intro a ha
      obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp ha
      rw [mul_smul,mul_smul,inv_smul_smul,hh b hb]
    · simp only [mul_smul,inv_smul_smul]

theorem acl_image_smul_iff (g : G) (A : Finset M) (x : M) :
    g • x ∈ Acl G (A.image (fun a => g • a)) ↔ x ∈ Acl G A := by
  change (orbitOver G _ _).Finite ↔ (orbitOver G _ _).Finite
  rw [orbitOver_image_smul]
  exact Set.finite_image_iff (MulAction.injective g).injOn

theorem closed_image_smul (g : G) (A : Finset M) (closed : Closed G A) :
    Closed G (A.image (fun a => g • a)) := by
  apply Set.Subset.antisymm
  · intro y hy
    have hx : g • (g⁻¹ • y) ∈ Acl G (A.image (fun a => g • a)) := by
      simpa only [smul_inv_smul] using hy
    have ha := (acl_image_smul_iff g A _).mp hx
    rw [closed] at ha
    exact Finset.mem_image.mpr ⟨g⁻¹ • y,ha,smul_inv_smul g y⟩
  · intro y hy
    exact parameter_mem_acl _ hy

/-- Fixing a finite set preserves membership in it in both directions. -/
theorem smul_mem_iff_of_fixes (g : G) (A : Finset M)
    (fixes : ∀ a ∈ A, g • a = a) (x : M) : g • x ∈ A ↔ x ∈ A := by
  constructor
  · intro hx
    have he : x = g • x := MulAction.injective g (fixes (g • x) hx).symm
    exact he ▸ hx
  · intro hx
    exact (fixes x hx).symm ▸ hx

end CCO.MIGeometry
