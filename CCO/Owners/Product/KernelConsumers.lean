import CCO.Owners.Product.ActionConsumers
import CCO.Owners.Product.Empty

/-! C26 assembles the kernel statements from the exact stated first-factor
onto/kernel input. Both actual source and nested target group identities
are retained, together with their true point-action compatibility. -/
namespace CCO.Owners.Product

namespace ProductGeometry
variable {G K ED JC O GT T : Type*} [Group G] [Group GT]
variable [MulAction G K] [MulAction G ED] [MulAction G JC] [MulAction G O] [MulAction GT T]
variable (P : ProductGeometry (G := G) (K := K) (ED := ED) (JC := JC) (O := O))
variable (D : Set ED) (C : Set JC) (B : Set O)
variable (hD : ∀ x : D, P.rD x.val ∈ B) (hC : ∀ x : C, P.rC x.val ∈ B)
variable (surjD : Function.Surjective (P.ownerD D B hD))
variable (surjC : Function.Surjective (P.ownerC C B hC))

theorem actual_nonnested_from_kernel [Nonempty (P.Carrier D C B hD hC)]
    (τ : OrbitalAut G ED (Subtype.val : D → ED) →* GT) (t : D → T)
    (eqT : ∀ g x, t (g • x) = τ g • t x) (surjT : Function.Surjective t)
    (first : Function.Surjective τ ∧ GroupActions.FibreTransitive τ t)
    (second : GroupActions.PrescribedLift (P.ownerActionC C B hC surjC) (P.ownerC C B hC)) :
    Function.Surjective
      ((matchingTarget (P.ownerActionD D B hD surjD) (P.ownerActionC C B hC surjC) τ).comp
        (P.fullAutEquiv D C B hD hC surjD surjC).toMonoidHom) ∧
    GroupActions.FibreTransitive
      ((matchingTarget (P.ownerActionD D B hD surjD) (P.ownerActionC C B hC surjC) τ).comp
        (P.fullAutEquiv D C B hD hC surjD surjC).toMonoidHom)
      (fun w : P.Carrier D C B hD hC => t w.val.1) := by
  letI : Nonempty D := ⟨(Classical.choice (inferInstance : Nonempty (P.Carrier D C B hD hC))).val.1⟩
  exact P.actual_nonnested_onto_kernel D C B hD hC surjD surjC τ t eqT surjT
    ((GroupActions.prescribed_action_point_lifting τ t surjT eqT).mp first) second

end ProductGeometry

section NestedActual
variable {GD GC GO GT GW GWT D C O T U V : Type*}
variable [Group GD] [Group GC] [Group GO] [Group GT] [Group GW] [Group GWT]
variable [MulAction GD D] [MulAction GC C] [MulAction GO O] [MulAction GT T]
variable [MulAction GW U] [MulAction GWT V] [FaithfulSMul GO O]

/-- Optional C21–22 with the ENTIRE supplied actual nested target group.
The displayed quotient q is literal. No C prescribed-point premise occurs. -/
theorem nested_actual_from_group_identities
    (ρD : GD →* GO) (ρC : GC →* GO) (τ : GD →* GT) (ρT : GT →* GO)
    (πD : D → O) (πC : C → O) (t : D → T) (s : T → O)
    (eqD : ∀ g x, πD (g • x) = ρD g • πD x)
    (eqC : ∀ g x, πC (g • x) = ρC g • πC x)
    (eqT : ∀ g x, t (g • x) = τ g • t x)
    (eqS : ∀ η x, s (η • x) = ρT η • s x)
    (factor : ∀ x, πD x = s (t x))
    (surjD : Function.Surjective πD) (surjT : Function.Surjective t)
    [Nonempty (Pullback πD πC)]
    (E : letI := pullbackAction ρD ρC πD πC eqD eqC
      ActionEquivalence GW (Matching ρD ρC) U (Pullback πD πC))
    (F : letI := pullbackAction ρT ρC s πC eqS eqC
      ActionEquivalence GWT (Matching ρT ρC) V (Pullback s πC))
    (q : U → V)
    (commutes : letI := pullbackAction ρD ρC πD πC eqD eqC
      letI := pullbackAction ρT ρC s πC eqS eqC
      ∀ x, F.point (q x) = nestedProjection πD πC t s factor (E.point x))
    (first : Function.Surjective τ ∧ GroupActions.FibreTransitive τ t) :
    letI := pullbackAction ρD ρC πD πC eqD eqC
    letI := pullbackAction ρT ρC s πC eqS eqC
    let compat := nested_owner_component ρD τ ρT πD t s eqD eqT eqS factor surjD
    Function.Surjective (E.transportedHom F (nestedTarget ρD ρC τ ρT compat)) ∧
      GroupActions.FibreTransitive (E.transportedHom F (nestedTarget ρD ρC τ ρT compat)) q := by
  letI := pullbackAction ρD ρC πD πC eqD eqC
  letI := pullbackAction ρT ρC s πC eqS eqC
  let compat := nested_owner_component ρD τ ρT πD t s eqD eqT eqS factor surjD
  letI : Nonempty D := ⟨(Classical.choice (inferInstance : Nonempty (Pullback πD πC))).val.1⟩
  apply E.onto_kernel_of_commuting F (nestedTarget ρD ρC τ ρT compat)
    (nestedProjection πD πC t s factor) q commutes
  exact onto_and_kernel_nested
    (ρD := ρD) (ρC := ρC) (τ := τ) (ρT := ρT)
    (πD := πD) (πC := πC) (t := t) (s := s)
    (eqD := eqD) (eqC := eqC) (eqT := eqT) (eqS := eqS) (factor := factor) surjT compat
    ((GroupActions.prescribed_action_point_lifting τ t surjT eqT).mp first)

end NestedActual
end CCO.Owners.Product
