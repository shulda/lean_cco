import CCO.Owners.Product.FullAutomorphisms
import CCO.Owners.Product.Nested

/-! Explicit transport from matching-pair groups to the actual full
automorphism actions. A group identity alone is insufficient: its point
action compatibility is displayed and is proved for the true product. -/
namespace CCO.Owners.Product

variable {K₁ K₂ H₁ H₂ X₁ X₂ Y₁ Y₂ : Type*}
variable [Group K₁] [Group K₂] [Group H₁] [Group H₂]
variable [MulAction K₁ X₁] [MulAction K₂ X₂] [MulAction H₁ Y₁] [MulAction H₂ Y₂]

structure ActionEquivalence (K₁ K₂ X₁ X₂ : Type*) [Group K₁] [Group K₂]
    [MulAction K₁ X₁] [MulAction K₂ X₂] where
  group : K₁ ≃* K₂
  point : X₁ ≃ X₂
  equivariant : ∀ g x, point (g • x) = group g • point x

namespace ActionEquivalence

variable (E : ActionEquivalence K₁ K₂ X₁ X₂) (F : ActionEquivalence H₁ H₂ Y₁ Y₂)

def refl (K X : Type*) [Group K] [MulAction K X] : ActionEquivalence K K X X where
  group := MulEquiv.refl _
  point := Equiv.refl _
  equivariant _ _ := rfl

def transportedHom (ρ : K₂ →* H₂) : K₁ →* H₁ :=
  F.group.symm.toMonoidHom.comp (ρ.comp E.group.toMonoidHom)

def transportedMap (π : X₂ → Y₂) : X₁ → Y₁ :=
  F.point.symm ∘ π ∘ E.point

@[simp] theorem transportedHom_commutes (ρ : K₂ →* H₂) (g : K₁) :
    F.group (E.transportedHom F ρ g) = ρ (E.group g) :=
  F.group.apply_symm_apply _

@[simp] theorem transportedMap_commutes (π : X₂ → Y₂) (x : X₁) :
    F.point (E.transportedMap F π x) = π (E.point x) :=
  F.point.apply_symm_apply _

theorem transportedMap_surjective (π : X₂ → Y₂) (surjπ : Function.Surjective π) :
    Function.Surjective (E.transportedMap F π) :=
  F.point.symm.surjective.comp (surjπ.comp E.point.surjective)

/-- The transported group map is the displayed induced map on actual
points; compatibility of both action identities is used explicitly. -/
theorem transported_equivariant (ρ : K₂ →* H₂) (π : X₂ → Y₂)
    (equivπ : ∀ g x, π (g • x) = ρ g • π x) (g : K₁) (x : X₁) :
    E.transportedMap F π (g • x) = E.transportedHom F ρ g • E.transportedMap F π x := by
  apply F.point.injective
  rw [F.equivariant,E.transportedMap_commutes,E.transportedHom_commutes,
    E.transportedMap_commutes,E.equivariant,equivπ]

/-- Transfer the ENTIRE prescribed target element, through both actual
full-group identities and both displayed point bijections. -/
theorem prescribed (ρ : K₂ →* H₂) (π : X₂ → Y₂)
    (h : GroupActions.PrescribedLift ρ π) :
    GroupActions.PrescribedLift (E.transportedHom F ρ) (E.transportedMap F π) := by
  intro x y η hη
  have hη' := congrArg F.point hη
  change F.point (η • F.point.symm (π (E.point x))) =
    F.point (F.point.symm (π (E.point y))) at hη'
  rw [F.equivariant] at hη'
  simp only [Equiv.apply_symm_apply] at hη'
  obtain ⟨g,hg,hmove⟩ := h (E.point x) (E.point y) (F.group η) hη'
  refine ⟨E.group.symm g,?_,?_⟩
  · change F.group.symm (ρ (E.group (E.group.symm g))) = η
    rw [MulEquiv.apply_symm_apply,hg,MulEquiv.symm_apply_apply]
  · apply E.point.injective
    rw [E.equivariant,MulEquiv.apply_symm_apply,hmove]

/-- Onto action and fibre transitivity transport directly; no nonempty
hypothesis is invented or discarded in this transport lemma. -/
theorem onto_kernel (ρ : K₂ →* H₂) (π : X₂ → Y₂)
    (h : Function.Surjective ρ ∧ GroupActions.FibreTransitive ρ π) :
    Function.Surjective (E.transportedHom F ρ) ∧
      GroupActions.FibreTransitive (E.transportedHom F ρ) (E.transportedMap F π) := by
  constructor
  · intro η
    obtain ⟨g,hg⟩ := h.1 (F.group η)
    refine ⟨E.group.symm g,?_⟩
    change F.group.symm (ρ (E.group (E.group.symm g))) = η
    rw [MulEquiv.apply_symm_apply,hg,MulEquiv.symm_apply_apply]
  · intro x y hxy
    have hxy' : π (E.point x) = π (E.point y) := F.point.symm.injective hxy
    obtain ⟨g,hg,hmove⟩ := h.2 (E.point x) (E.point y) hxy'
    refine ⟨E.group.symm g,?_,?_⟩
    · change F.group.symm (ρ (E.group (E.group.symm g))) = 1
      rw [MulEquiv.apply_symm_apply,hg]
      exact F.group.symm.map_one
    · apply E.point.injective
      rw [E.equivariant,MulEquiv.apply_symm_apply,hmove]

/-- The displayed original quotient map may be kept literally, rather
than replaced by a transported-map definition. -/
theorem prescribed_of_commuting (ρ : K₂ →* H₂) (π : X₂ → Y₂) (q : X₁ → Y₁)
    (commutes : ∀ x, F.point (q x) = π (E.point x))
    (h : GroupActions.PrescribedLift ρ π) :
    GroupActions.PrescribedLift (E.transportedHom F ρ) q := by
  have hq : q = E.transportedMap F π := by
    funext x
    exact (F.point.symm_apply_apply (q x)).symm.trans (congrArg F.point.symm (commutes x))
  rw [hq]
  exact E.prescribed F ρ π h

theorem onto_kernel_of_commuting (ρ : K₂ →* H₂) (π : X₂ → Y₂) (q : X₁ → Y₁)
    (commutes : ∀ x, F.point (q x) = π (E.point x))
    (h : Function.Surjective ρ ∧ GroupActions.FibreTransitive ρ π) :
    Function.Surjective (E.transportedHom F ρ) ∧
      GroupActions.FibreTransitive (E.transportedHom F ρ) q := by
  have hq : q = E.transportedMap F π := by
    funext x
    exact (F.point.symm_apply_apply (q x)).symm.trans (congrArg F.point.symm (commutes x))
  rw [hq]
  exact E.onto_kernel F ρ π h

end ActionEquivalence

namespace ProductGeometry
variable {G K ED JC O : Type*} [Group G]
variable [MulAction G K] [MulAction G ED] [MulAction G JC] [MulAction G O]
variable (P : ProductGeometry (G := G) (K := K) (ED := ED) (JC := JC) (O := O))
variable (D : Set ED) (C : Set JC) (B : Set O)
variable (hD : ∀ x : D, P.rD x.val ∈ B) (hC : ∀ x : C, P.rC x.val ∈ B)
variable (surjD : Function.Surjective (P.ownerD D B hD))
variable (surjC : Function.Surjective (P.ownerC C B hC))

/-- The actual C17 identity is compatible with the actual permutation
point action, not merely an abstract isomorphism of unnamed groups. -/
noncomputable def fullAutActionEquivalence :
    letI := pullbackAction (P.ownerActionD D B hD surjD) (P.ownerActionC C B hC surjC)
      (P.ownerD D B hD) (P.ownerC C B hC)
      (fun g x => ((P.quotientOwnerD D B hD surjD).action_projection g x).symm)
      (fun g x => ((P.quotientOwnerC C B hC surjC).action_projection g x).symm)
    ActionEquivalence (OrbitalAut G K (P.point D C B hD hC))
      (Matching (P.ownerActionD D B hD surjD) (P.ownerActionC C B hC surjC))
      (P.Carrier D C B hD hC) (P.Carrier D C B hD hC) := by
  letI := pullbackAction (P.ownerActionD D B hD surjD) (P.ownerActionC C B hC surjC)
    (P.ownerD D B hD) (P.ownerC C B hC)
    (fun g x => ((P.quotientOwnerD D B hD surjD).action_projection g x).symm)
    (fun g x => ((P.quotientOwnerC C B hC surjC).action_projection g x).symm)
  refine ⟨P.fullAutEquiv D C B hD hC surjD surjC,Equiv.refl _,?_⟩
  intro g w
  apply Subtype.ext
  apply Prod.ext
  · exact ((P.quotientD D C B hD hC surjC).action_projection g w).symm
  · exact ((P.quotientC D C B hD hC surjD).action_projection g w).symm

variable {GT T : Type*} [Group GT] [MulAction GT T]

/-- C20 for the ACTUAL full fine-coloured automorphism group, through
its proved natural action identity. The only point premises are the
prescribed D-to-T and C-to-O point properties of the source statement. -/
theorem actual_nonnested_onto_kernel
    [Nonempty (P.Carrier D C B hD hC)]
    (τ : OrbitalAut G ED (Subtype.val : D → ED) →* GT) (t : D → T)
    (eqT : ∀ g x, t (g • x) = τ g • t x)
    (surjT : Function.Surjective t)
    (liftD : GroupActions.PrescribedLift τ t)
    (liftC : GroupActions.PrescribedLift (P.ownerActionC C B hC surjC)
      (P.ownerC C B hC)) :
    Function.Surjective
      ((matchingTarget (P.ownerActionD D B hD surjD) (P.ownerActionC C B hC surjC) τ).comp
        (P.fullAutEquiv D C B hD hC surjD surjC).toMonoidHom) ∧
    GroupActions.FibreTransitive
      ((matchingTarget (P.ownerActionD D B hD surjD) (P.ownerActionC C B hC surjC) τ).comp
        (P.fullAutEquiv D C B hD hC surjD surjC).toMonoidHom)
      (fun w : P.Carrier D C B hD hC => t w.val.1) := by
  letI := pullbackAction (P.ownerActionD D B hD surjD) (P.ownerActionC C B hC surjC)
    (P.ownerD D B hD) (P.ownerC C B hC)
    (fun g x => ((P.quotientOwnerD D B hD surjD).action_projection g x).symm)
    (fun g x => ((P.quotientOwnerC C B hC surjC).action_projection g x).symm)
  let E := P.fullAutActionEquivalence D C B hD hC surjD surjC
  let F := ActionEquivalence.refl GT T
  have h := onto_and_kernel_nonnested
    (P.ownerActionD D B hD surjD) (P.ownerActionC C B hC surjC)
    (P.ownerD D B hD) (P.ownerC C B hC)
    (fun g x => ((P.quotientOwnerD D B hD surjD).action_projection g x).symm)
    (fun g x => ((P.quotientOwnerC C B hC surjC).action_projection g x).symm)
    τ t eqT surjC surjT liftD liftC
  exact E.onto_kernel_of_commuting F
    (matchingTarget (P.ownerActionD D B hD surjD) (P.ownerActionC C B hC surjC) τ)
    (fun w : P.Carrier D C B hD hC => t w.val.1)
    (fun w : P.Carrier D C B hD hC => t w.val.1) (fun _ => rfl) h

end ProductGeometry
end CCO.Owners.Product
