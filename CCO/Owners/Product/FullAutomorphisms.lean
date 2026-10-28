import CCO.Owners.Product.FullGeometry

/-! Actual full automorphisms of the full fine-coloured product. -/
namespace CCO.Owners.Product.ProductGeometry

variable {G K ED JC O : Type*} [Group G]
variable [MulAction G K] [MulAction G ED] [MulAction G JC] [MulAction G O]
variable (P : ProductGeometry (G := G) (K := K) (ED := ED) (JC := JC) (O := O))
variable (D : Set ED) (C : Set JC) (B : Set O)
variable (hD : ∀ x : D, P.rD x.val ∈ B) (hC : ∀ x : C, P.rC x.val ∈ B)
variable (surjD : Function.Surjective (P.ownerD D B hD))
variable (surjC : Function.Surjective (P.ownerC C B hC))

noncomputable def ownerActionD := (P.quotientOwnerD D B hD surjD).action
noncomputable def ownerActionC := (P.quotientOwnerC C B hC surjC).action

noncomputable def restriction :
    OrbitalAut G K (P.point D C B hD hC) →*
      Matching (P.ownerActionD D B hD surjD) (P.ownerActionC C B hC surjC) where
  toFun f := ⟨((P.quotientD D C B hD hC surjC).action f,
    (P.quotientC D C B hD hC surjD).action f),by
    apply Subtype.ext
    apply Equiv.ext
    intro b
    obtain ⟨d,rfl⟩ := surjD b
    obtain ⟨w,hw⟩ := pullback_fst_surjective (P.ownerD D B hD) (P.ownerC C B hC) surjC d
    subst d
    change ((P.quotientOwnerD D B hD surjD).action
      ((P.quotientD D C B hD hC surjC).action f)).val (P.ownerD D B hD w.val.1) =
      ((P.quotientOwnerC C B hC surjC).action
      ((P.quotientC D C B hD hC surjD).action f)).val (P.ownerD D B hD w.val.1)
    calc
      _ = P.ownerD D B hD (((P.quotientD D C B hD hC surjC).action f).val w.val.1) :=
        (P.quotientOwnerD D B hD surjD).action_projection _ _
      _ = P.ownerD D B hD (f.val w).val.1 := congrArg (P.ownerD D B hD)
        ((P.quotientD D C B hD hC surjC).action_projection f w)
      _ = P.ownerC C B hC (f.val w).val.2 := (f.val w).property
      _ = P.ownerC C B hC (((P.quotientC D C B hD hC surjD).action f).val w.val.2) :=
        congrArg (P.ownerC C B hC) ((P.quotientC D C B hD hC surjD).action_projection f w).symm
      _ = ((P.quotientOwnerC C B hC surjC).action
        ((P.quotientC D C B hD hC surjD).action f)).val (P.ownerC C B hC w.val.2) :=
        ((P.quotientOwnerC C B hC surjC).action_projection _ _).symm
      _ = _ := congrArg _ w.property.symm⟩
  map_one' := by apply Subtype.ext; exact Prod.ext (map_one _) (map_one _)
  map_mul' f g := by apply Subtype.ext; exact Prod.ext (map_mul _ _ _) (map_mul _ _ _)

noncomputable def lift :
    Matching (P.ownerActionD D B hD surjD) (P.ownerActionC C B hC surjC) →*
      OrbitalAut G K (P.point D C B hD hC) := by
  letI := pullbackAction (P.ownerActionD D B hD surjD) (P.ownerActionC C B hC surjC)
    (P.ownerD D B hD) (P.ownerC C B hC)
    (fun g x => ((P.quotientOwnerD D B hD surjD).action_projection g x).symm)
    (fun g x => ((P.quotientOwnerC C B hC surjC).action_projection g x).symm)
  refine {
    toFun := fun k => ⟨MulAction.toPerm k,?_⟩
    map_one' := ?_
    map_mul' := ?_ }
  · apply (mem_orbitalAut_iff _).mpr
    intro w v
    apply (P.fine _ _ _ _).mp
    constructor
    · simp only [P.pD_point]
      exact orbitalAut_pair k.val.1 w.val.1 v.val.1
    · simp only [P.pC_point]
      exact orbitalAut_pair k.val.2 w.val.2 v.val.2
  · apply Subtype.ext
    exact (MulAction.toPermHom _ _).map_one
  · intro k l
    apply Subtype.ext
    exact (MulAction.toPermHom _ _).map_mul k l

@[simp] theorem lift_apply_fst
    (k : Matching (P.ownerActionD D B hD surjD) (P.ownerActionC C B hC surjC))
    (w : P.Carrier D C B hD hC) :
    ((P.lift D C B hD hC surjD surjC k).val w).val.1 = k.val.1.val w.val.1 := rfl
@[simp] theorem lift_apply_snd
    (k : Matching (P.ownerActionD D B hD surjD) (P.ownerActionC C B hC surjC))
    (w : P.Carrier D C B hD hC) :
    ((P.lift D C B hD hC surjD surjC k).val w).val.2 = k.val.2.val w.val.2 := rfl

@[simp] theorem lift_restriction (f : OrbitalAut G K (P.point D C B hD hC)) :
    P.lift D C B hD hC surjD surjC (P.restriction D C B hD hC surjD surjC f) = f := by
  apply Subtype.ext
  apply Equiv.ext
  intro w
  apply Subtype.ext
  apply Prod.ext
  · exact (P.quotientD D C B hD hC surjC).action_projection f w
  · exact (P.quotientC D C B hD hC surjD).action_projection f w

@[simp] theorem restriction_lift
    (k : Matching (P.ownerActionD D B hD surjD) (P.ownerActionC C B hC surjC)) :
    P.restriction D C B hD hC surjD surjC (P.lift D C B hD hC surjD surjC k) = k := by
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    apply Equiv.ext
    intro d
    obtain ⟨w,rfl⟩ := pullback_fst_surjective (P.ownerD D B hD) (P.ownerC C B hC) surjC d
    change ((P.quotientD D C B hD hC surjC).action _).val
      ((P.quotientD D C B hD hC surjC).projection w) = _
    rw [OrbitalQuotient.action_projection]
    rfl
  · apply Subtype.ext
    apply Equiv.ext
    intro c
    obtain ⟨w,rfl⟩ := pullback_snd_surjective (P.ownerD D B hD) (P.ownerC C B hC) surjD c
    change ((P.quotientC D C B hD hC surjD).action _).val
      ((P.quotientC D C B hD hC surjD).projection w) = _
    rw [OrbitalQuotient.action_projection]
    rfl

/-- C17: the natural full-coloured automorphism group isomorphism.
No extension to the ambient source and no group section is used. -/
noncomputable def fullAutEquiv :
    OrbitalAut G K (P.point D C B hD hC) ≃*
      Matching (P.ownerActionD D B hD surjD) (P.ownerActionC C B hC surjC) where
  toFun := P.restriction D C B hD hC surjD surjC
  invFun := P.lift D C B hD hC surjD surjC
  left_inv := P.lift_restriction D C B hD hC surjD surjC
  right_inv := P.restriction_lift D C B hD hC surjD surjC
  map_mul' := (P.restriction D C B hD hC surjD surjC).map_mul

end CCO.Owners.Product.ProductGeometry
