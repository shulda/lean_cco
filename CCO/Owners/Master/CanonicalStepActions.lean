import CCO.Owners.Master.SourceProduct
import CCO.Owners.Master.StepActionEquivalence

/-! The full product action with all components rewritten as the genuine
canonical stage maps and the ONE chosen local owner action. This common
identity is used separately for the largest and every new target. -/

universe v w t z
namespace CCO.Owners.Master
noncomputable section
open RawExact ExactCRT Provider Product

section Congruence
variable {GD GC GO D C O : Type*} [Group GD] [Group GC] [Group GO]
variable [MulAction GD D] [MulAction GC C] [MulAction GO O]

def matchingGroupCongr (ρD σD : GD →* GO) (ρC σC : GC →* GO)
    (hD : ρD = σD) (hC : ρC = σC) : Matching ρD ρC ≃* Matching σD σC where
  toFun g := ⟨g.val,by
    change σD g.val.1 = σC g.val.2
    rw [← hD,← hC]
    exact g.property⟩
  invFun g := ⟨g.val,by
    change ρD g.val.1 = ρC g.val.2
    rw [hD,hC]
    exact g.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

def pullbackPointCongr (πD τD : D → O) (πC τC : C → O)
    (hD : πD = τD) (hC : πC = τC) : Pullback πD πC ≃ Pullback τD τC where
  toFun x := ⟨x.val,by
    change τD x.val.1 = τC x.val.2
    rw [← hD,← hC]
    exact x.property⟩
  invFun x := ⟨x.val,by
    change πD x.val.1 = πC x.val.2
    rw [hD,hC]
    exact x.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

/-- Equal canonical components give an action identity by the literal
same coordinate pairs, avoiding dependent casts of pullback actions. -/
def pullbackActionCongr (ρD σD : GD →* GO) (ρC σC : GC →* GO)
    (πD τD : D → O) (πC τC : C → O)
    (eqD : ∀ g x, πD (g • x) = ρD g • πD x)
    (eqC : ∀ g x, πC (g • x) = ρC g • πC x)
    (eqD' : ∀ g x, τD (g • x) = σD g • τD x)
    (eqC' : ∀ g x, τC (g • x) = σC g • τC x)
    (hρD : ρD = σD) (hρC : ρC = σC) (hπD : πD = τD) (hπC : πC = τC) :
    letI := pullbackAction ρD ρC πD πC eqD eqC
    letI := pullbackAction σD σC τD τC eqD' eqC'
    ActionEquivalence (Matching ρD ρC) (Matching σD σC)
      (Pullback πD πC) (Pullback τD τC) := by
  letI := pullbackAction ρD ρC πD πC eqD eqC
  letI := pullbackAction σD σC τD τC eqD' eqC'
  refine ⟨matchingGroupCongr ρD σD ρC σC hρD hρC,
    pullbackPointCongr πD τD πC τC hπD hπC,?_⟩
  intro g x
  apply Subtype.ext
  apply Prod.ext <;> rfl
end Congruence

variable {A : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => A))
variable {G : Type t} [Group G] [MulAction G A] [Countable A]
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,v,w} S)
variable {T : Set A} {U : Finset (Position S H cco)}
variable (B : SourceStage.{v,w,t,z} S H cco T U)
variable {p : Position S H cco} (next : Next U p) (upU : IsUpset U)
variable (W : LocalFactor S H cco B next)
variable (V : Finset (Position S H cco)) (upV : IsUpset V)
variable (within : V ⊆ insert p U) (hp : p ∈ V)

local instance canonicalMatchingAction :
    let Q := stageQuotient S H cco B.finite (next_erase_upset upU next upV within)
      (strictUpper_upset p) (next_erase_subset within)
      (next_strictUpper_subset_erase upV hp)
    MulAction (Matching Q.action W.quotient.action)
      (Pullback Q.projection W.quotient.projection) := by
  let Q := stageQuotient S H cco B.finite (next_erase_upset upU next upV within)
    (strictUpper_upset p) (next_erase_subset within)
    (next_strictUpper_subset_erase upV hp)
  exact pullbackAction Q.action W.quotient.action Q.projection W.quotient.projection
    (fun g x => (Q.action_projection g x).symm)
    (fun g x => (W.quotient.action_projection g x).symm)

def canonicalStepAction :
    let Q := stageQuotient S H cco B.finite (next_erase_upset upU next upV within)
      (strictUpper_upset p) (next_erase_subset within)
      (next_strictUpper_subset_erase upV hp)
    letI := pullbackAction Q.action W.quotient.action Q.projection W.quotient.projection
      (fun g x => (Q.action_projection g x).symm)
      (fun g x => (W.quotient.action_projection g x).symm)
    ActionEquivalence
      (OrbitalAut G (Coordinate S H cco V)
        (Subtype.val : (sourceStep S H cco B next upU W).stage.B V → _))
      (Matching Q.action W.quotient.action)
      ((sourceStep S H cco B next upU W).stage.B V)
      (Pullback Q.projection W.quotient.projection) := by
  let P := stepGeometry S H cco upU next upV within hp
  let D := B.finite.B (V.erase p)
  let C := W.carrier
  let O := B.finite.B (strictUpper p)
  let hD := stepOldOwner S H cco B next upU V upV within hp
  let hC := stepLocalOwner S H cco B next upU W V upV within hp
  let ontoD := stepOldOwnerOnto S H cco B next upU V upV within hp
  let ontoC := stepLocalOwnerOnto S H cco B next upU W V upV within hp
  let e := stepPointEquiv S H cco B next upU W V upV within hp
  letI := pullbackAction (P.ownerActionD D O hD ontoD) (P.ownerActionC C O hC ontoC)
    (P.ownerD D O hD) (P.ownerC C O hC)
    (fun g x => ((P.quotientOwnerD D O hD ontoD).action_projection g x).symm)
    (fun g x => ((P.quotientOwnerC C O hC ontoC).action_projection g x).symm)
  let E := product_action_equivalence P D C O hD hC ontoD ontoC
    (Subtype.val : (sourceStep S H cco B next upU W).stage.B V → _) e
    (stepPointEquiv_val S H cco B next upU W V upV within hp)
  let Q := stageQuotient S H cco B.finite (next_erase_upset upU next upV within)
    (strictUpper_upset p) (next_erase_subset within)
    (next_strictUpper_subset_erase upV hp)
  letI := pullbackAction Q.action W.quotient.action Q.projection W.quotient.projection
    (fun g x => (Q.action_projection g x).symm)
    (fun g x => (W.quotient.action_projection g x).symm)
  let F := pullbackActionCongr
    (P.ownerActionD D O hD ontoD) Q.action (P.ownerActionC C O hC ontoC) W.quotient.action
    (P.ownerD D O hD) Q.projection (P.ownerC C O hC) W.quotient.projection
    (fun g x => ((P.quotientOwnerD D O hD ontoD).action_projection g x).symm)
    (fun g x => ((P.quotientOwnerC C O hC ontoC).action_projection g x).symm)
    (fun g x => (Q.action_projection g x).symm)
    (fun g x => (W.quotient.action_projection g x).symm)
    (stepOldOwnerAction S H cco B next upU V upV within hp)
    (stepLocalOwnerAction S H cco B next upU W V upV within hp)
    (stepOldOwner_projection S H cco B next upU V upV within hp)
    (stepLocalOwner_projection S H cco B next upU W V upV within hp)
  refine ⟨E.group.trans F.group,E.point.trans F.point,?_⟩
  intro g x
  change F.point (E.point (g • x)) = F.group (E.group g) • F.point (E.point x)
  rw [E.equivariant,F.equivariant]

@[simp] theorem canonicalStepAction_point_val
    (x : (sourceStep S H cco B next upU W).stage.B V) :
    letI := canonicalMatchingAction S H cco B next upU W V upV within hp
    ((canonicalStepAction S H cco B next upU W V upV within hp).point x).val =
      ((stepPointEquiv S H cco B next upU W V upV within hp).symm x).val := rfl

theorem canonicalStepAction_fst
    (x : (sourceStep S H cco B next upU W).stage.B V) :
    letI := canonicalMatchingAction S H cco B next upU W V upV within hp
    ((canonicalStepAction S H cco B next upU W V upV within hp).point x).val.1.val =
      coordinateMap S H cco (Finset.erase_subset p V) x.val := by
  rw [canonicalStepAction_point_val]
  let e := stepPointEquiv S H cco B next upU W V upV within hp
  have hh := stepPointEquiv_fst S H cco B next upU W V upV within hp (e.symm x)
  change coordinateMap S H cco (Finset.erase_subset p V) (e (e.symm x)).val = _ at hh
  rw [e.apply_symm_apply] at hh
  exact hh.symm

theorem canonicalStepAction_snd
    (x : (sourceStep S H cco B next upU W).stage.B V) :
    letI := canonicalMatchingAction S H cco B next upU W V upV within hp
    ((canonicalStepAction S H cco B next upU W V upV within hp).point x).val.2.val =
      coordinateMap S H cco
        ((sourceStep S H cco B next upU W).principal_subset upV within hp) x.val := by
  rw [canonicalStepAction_point_val]
  let e := stepPointEquiv S H cco B next upU W V upV within hp
  have hh := stepPointEquiv_snd S H cco B next upU W V upV within hp (e.symm x)
  change coordinateMap S H cco
    ((sourceStep S H cco B next upU W).principal_subset upV within hp)
      (e (e.symm x)).val = _ at hh
  rw [e.apply_symm_apply] at hh
  exact hh.symm

end
end CCO.Owners.Master
