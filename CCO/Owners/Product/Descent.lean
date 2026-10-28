import CCO.Owners.Product.Orbitals

/-! Actual coordinate descent for full and sparse orbital maps. -/
namespace CCO.Owners.Product

variable {G A B U V : Type*} [Group G] [MulAction G A] [MulAction G B]

structure OrbitalQuotient (ι : U → A) (κ : V → B) where
  ambient : A → B
  equivariant : ∀ (g : G) x, ambient (g • x) = g • ambient x
  projection : U → V
  surjective : Function.Surjective projection
  target_injective : Function.Injective κ
  commutes : ∀ x, κ (projection x) = ambient (ι x)

namespace OrbitalQuotient
variable {ι : U → A} {κ : V → B} (Q : OrbitalQuotient (G := G) ι κ)

theorem kernel_iff (g : OrbitalAut G A ι) (x y : U) :
    Q.projection (g.val x) = Q.projection (g.val y) ↔
      Q.projection x = Q.projection y := by
  rw [← Q.target_injective.eq_iff, ← Q.target_injective.eq_iff]
  simp only [Q.commutes]
  exact equivariant_kernel_iff Q.ambient Q.equivariant (orbitalAut_pair g x y)

noncomputable def map (g : OrbitalAut G A ι) (y : V) : V :=
  Q.projection (g.val (Classical.choose (Q.surjective y)))

@[simp] theorem map_projection (g : OrbitalAut G A ι) (x : U) :
    Q.map g (Q.projection x) = Q.projection (g.val x) :=
  (Q.kernel_iff g _ x).mpr (Classical.choose_spec (Q.surjective (Q.projection x)))

noncomputable def perm (g : OrbitalAut G A ι) : Equiv.Perm V where
  toFun := Q.map g
  invFun := Q.map g⁻¹
  left_inv := by
    intro y
    obtain ⟨x,rfl⟩ := Q.surjective y
    rw [Q.map_projection, Q.map_projection]
    simp
  right_inv := by
    intro y
    obtain ⟨x,rfl⟩ := Q.surjective y
    rw [Q.map_projection, Q.map_projection]
    simp

noncomputable def aut (g : OrbitalAut G A ι) : OrbitalAut G B κ := by
  refine ⟨Q.perm g, (mem_orbitalAut_iff _).mpr ?_⟩
  intro x y
  obtain ⟨a,rfl⟩ := Q.surjective x
  obtain ⟨b,rfl⟩ := Q.surjective y
  change GroupActions.orbital (G := G) (κ (Q.projection a)) (κ (Q.projection b))
    (κ (Q.map g (Q.projection a))) (κ (Q.map g (Q.projection b)))
  rw [Q.map_projection,Q.map_projection]
  simp only [Q.commutes]
  exact equivariant_pair Q.ambient Q.equivariant (orbitalAut_pair g a b)

@[simp] theorem aut_projection (g : OrbitalAut G A ι) (x : U) :
    (Q.aut g).val (Q.projection x) = Q.projection (g.val x) := Q.map_projection g x

noncomputable def action : OrbitalAut G A ι →* OrbitalAut G B κ where
  toFun := Q.aut
  map_one' := by
    apply Subtype.ext
    ext y
    obtain ⟨x,rfl⟩ := Q.surjective y
    exact Q.aut_projection 1 x
  map_mul' := by
    intro g h
    apply Subtype.ext
    ext y
    obtain ⟨x,rfl⟩ := Q.surjective y
    change (Q.aut (g*h)).val (Q.projection x) = (Q.aut g).val ((Q.aut h).val (Q.projection x))
    rw [Q.aut_projection,Q.aut_projection,Q.aut_projection]
    rfl

@[simp] theorem action_projection (g : OrbitalAut G A ι) (x : U) :
    (Q.action g).val (Q.projection x) = Q.projection (g.val x) := Q.aut_projection g x

end OrbitalQuotient
end CCO.Owners.Product
