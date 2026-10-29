import CCO.Owners.Master.CanonicalStepActions
import CCO.Owners.Master.ActionNaturality
import CCO.Owners.Master.StageActions
import CCO.Owners.Product.KernelConsumers

/-! A new target retains its own FULL product automorphism group. The
whole target pair, including its prescribed local-factor component, is
lifted; no local prescribed-point input is used in this nested branch. -/

universe v w t z
namespace CCO.Owners.Master
noncomputable section
open RawExact ExactCRT Provider Product

variable {A : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => A))
variable {G : Type t} [Group G] [MulAction G A] [Countable A]
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,v,w} S)
variable {T : Set A} {U : Finset (Position S H cco)}
variable (B : SourceStage.{v,w,t,z} S H cco T U)
variable {p : Position S H cco} (next : Next U p)

theorem sourceStep_new_prescribed (upU : IsUpset U) (W : LocalFactor S H cco B next)
    (V Z : Finset (Position S H cco)) (upV : IsUpset V) (upZ : IsUpset Z)
    (within : V ⊆ insert p U) (hZV : Z ⊆ V) (hpZ : p ∈ Z) :
    let C := (sourceStep S H cco B next upU W).stage
    GroupActions.PrescribedLift (stageQuotient S H cco C upV upZ within hZV).action
      (C.r upV upZ within hZV) := by
  let C := (sourceStep S H cco B next upU W).stage
  have hpV : p ∈ V := hZV hpZ
  have withinZ : Z ⊆ insert p U := hZV.trans within
  let upD := next_erase_upset upU next upV within
  let upTarget := next_erase_upset upU next upZ withinZ
  let oldWithin := next_erase_subset within
  let oldTargetWithin := next_erase_subset withinZ
  let hTD : Z.erase p ⊆ V.erase p := Finset.erase_subset_erase p hZV
  let hOD : strictUpper p ⊆ V.erase p := next_strictUpper_subset_erase upV hpV
  let hOT : strictUpper p ⊆ Z.erase p := next_strictUpper_subset_erase upZ hpZ
  let QD := stageQuotient S H cco B.finite upD (strictUpper_upset p) oldWithin hOD
  let QT := stageQuotient S H cco B.finite upTarget (strictUpper_upset p) oldTargetWithin hOT
  let QDT := stageQuotient S H cco B.finite upD upTarget oldWithin hTD
  let ρD := QD.action
  let ρC := W.quotient.action
  let ρT := QT.action
  let τ := QDT.action
  let πD := QD.projection
  let πC := W.quotient.projection
  let target := QDT.projection
  let owner := QT.projection
  let eqD := fun g x => (QD.action_projection g x).symm
  let eqC := fun g x => (W.quotient.action_projection g x).symm
  let eqT := fun g x => (QDT.action_projection g x).symm
  let eqOwner := fun g x => (QT.action_projection g x).symm
  have factor : ∀ x, πD x = owner (target x) := by
    intro x
    exact (B.finite.r_comp upD upTarget (strictUpper_upset p) oldWithin hTD hOT x).symm
  have compat : ∀ g, ρT (τ g) = ρD g := by
    intro g
    exact B.finite.action_comp_apply (G := G)
      (fun {V W} h g x => coordinateMap_equivariant S H cco h g x)
      upD upTarget (strictUpper_upset p) oldWithin hTD hOT g
  letI := pullbackAction ρD ρC πD πC eqD eqC
  letI := pullbackAction ρT ρC owner πC eqOwner eqC
  let E := canonicalStepAction S H cco B next upU W V upV within hpV
  let F := canonicalStepAction S H cco B next upU W Z upZ withinZ hpZ
  let Q := stageQuotient S H cco C upV upZ within hZV
  let ρ := nestedTarget ρD ρC τ ρT compat
  let π := nestedProjection πD πC target owner factor
  letI : Nonempty (B.finite.B (V.erase p)) := by
    obtain ⟨x,hx⟩ := B.finite.nonempty (V.erase p) upD oldWithin
    exact ⟨⟨x,hx⟩⟩
  have liftD : GroupActions.PrescribedLift τ target :=
    (GroupActions.prescribed_action_point_lifting τ target QDT.surjective eqT).mp
      (B.decorations.m3 upD upTarget oldWithin hTD)
  have nested : GroupActions.PrescribedLift ρ π :=
    prescribed_nested ρD ρC τ ρT πD πC target owner eqD eqC eqOwner factor compat liftD
  have equivπ : ∀ g x, π (g • x) = ρ g • π x := by
    intro g x
    apply Subtype.ext
    exact Prod.ext (eqT g.val.1 x.val.1) rfl
  have commutes : ∀ x, F.point (Q.projection x) = π (E.point x) := by
    intro x
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      rw [canonicalStepAction_fst]
      change coordinateMap S H cco (Finset.erase_subset p Z)
        (coordinateMap S H cco hZV x.val) =
          coordinateMap S H cco hTD (E.point x).val.1.val
      rw [canonicalStepAction_fst]
      exact (coordinateMap_comp S H cco hZV (Finset.erase_subset p Z) x.val).trans
        (coordinateMap_comp S H cco (Finset.erase_subset p V) hTD x.val).symm
    · apply Subtype.ext
      rw [canonicalStepAction_snd]
      change coordinateMap S H cco
        ((sourceStep S H cco B next upU W).principal_subset upZ withinZ hpZ)
        (coordinateMap S H cco hZV x.val) = (E.point x).val.2.val
      rw [canonicalStepAction_snd]
      exact coordinateMap_comp S H cco hZV
        ((sourceStep S H cco B next upU W).principal_subset upZ withinZ hpZ) x.val
  exact actual_prescribed_of_commuting Q E F ρ π equivπ commutes nested

theorem sourceStep_new_m3 (upU : IsUpset U) (W : LocalFactor S H cco B next)
    (V Z : Finset (Position S H cco)) (upV : IsUpset V) (upZ : IsUpset Z)
    (within : V ⊆ insert p U) (hZV : Z ⊆ V) (hpZ : p ∈ Z) :
    let C := (sourceStep S H cco B next upU W).stage
    Function.Surjective (stageQuotient S H cco C upV upZ within hZV).action ∧
      GroupActions.FibreTransitive (stageQuotient S H cco C upV upZ within hZV).action
        (C.r upV upZ within hZV) := by
  let C := (sourceStep S H cco B next upU W).stage
  let Q := stageQuotient S H cco C upV upZ within hZV
  letI : Nonempty (C.B V) := by
    obtain ⟨x,hx⟩ := C.nonempty V upV within
    exact ⟨⟨x,hx⟩⟩
  exact (GroupActions.prescribed_action_point_lifting Q.action Q.projection Q.surjective
    (fun g x => (Q.action_projection g x).symm)).mpr
      (sourceStep_new_prescribed S H cco B next upU W V Z upV upZ within hZV hpZ)

end
end CCO.Owners.Master
