import CCO.Owners.Master.SourceProduct
import CCO.Owners.Master.StepActionEquivalence
import CCO.Owners.Master.ActionNaturality
import CCO.Owners.Product.KernelConsumers

/-! Full finite actions from a new object to every old target. The old
target need not contain the new owner upset: the second factor receives
the ACTUAL owner component of the first-factor lift. -/

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

/-- C18, in the stronger form for every new source object and any old
target below its old factor. No map from that target to the owner is used. -/
theorem sourceStep_old_m3 (upU : IsUpset U) (W : LocalFactor S H cco B next)
    (V Z : Finset (Position S H cco)) (upV : IsUpset V) (upZ : IsUpset Z)
    (within : V ⊆ insert p U) (hp : p ∈ V) (hZV : Z ⊆ V.erase p) :
    let C := (sourceStep S H cco B next upU W).stage
    Function.Surjective (stageQuotient S H cco C upV upZ within
      (hZV.trans (Finset.erase_subset p V))).action ∧
      GroupActions.FibreTransitive (stageQuotient S H cco C upV upZ within
        (hZV.trans (Finset.erase_subset p V))).action
        (C.r upV upZ within (hZV.trans (Finset.erase_subset p V))) := by
  let C := (sourceStep S H cco B next upU W).stage
  let P := stepGeometry S H cco upU next upV within hp
  let D := B.finite.B (V.erase p)
  let O := B.finite.B (strictUpper p)
  let hD := stepOldOwner S H cco B next upU V upV within hp
  let hC := stepLocalOwner S H cco B next upU W V upV within hp
  let ontoD := stepOldOwnerOnto S H cco B next upU V upV within hp
  let ontoC := stepLocalOwnerOnto S H cco B next upU W V upV within hp
  let ρD := P.ownerActionD D O hD ontoD
  let ρC := P.ownerActionC W.carrier O hC ontoC
  let πD := P.ownerD D O hD
  let πC := P.ownerC W.carrier O hC
  let eqD := fun g x => ((P.quotientOwnerD D O hD ontoD).action_projection g x).symm
  let eqC := fun g x => ((P.quotientOwnerC W.carrier O hC ontoC).action_projection g x).symm
  letI := pullbackAction ρD ρC πD πC eqD eqC
  let upD := next_erase_upset upU next upV within
  let oldWithin := next_erase_subset within
  let Qold := stageQuotient S H cco B.finite upD upZ oldWithin hZV
  let τ := Qold.action
  let target := B.finite.r upD upZ oldWithin hZV
  let eqTarget := fun g x => (Qold.action_projection g x).symm
  let e := stepPointEquiv S H cco B next upU W V upV within hp
  let E := product_action_equivalence P D W.carrier O hD hC ontoD ontoC
    (Subtype.val : C.B V → Coordinate S H cco V) e
    (stepPointEquiv_val S H cco B next upU W V upV within hp)
  have oldZ : Z ⊆ U := hZV.trans oldWithin
  let eZ : C.B Z ≃ B.finite.B Z :=
    Set.equivOfEq ((sourceStep S H cco B next upU W).stage_old Z oldZ)
  let F := orbital_action_equivalence (G₀ := G)
    (Subtype.val : C.B Z → Coordinate S H cco Z)
    (Subtype.val : B.finite.B Z → Coordinate S H cco Z) eZ (fun _ => rfl)
  let Q := stageQuotient S H cco C upV upZ within
    (hZV.trans (Finset.erase_subset p V))
  let ρ := matchingTarget ρD ρC τ
  let π := fun x : P.Carrier D W.carrier O hD hC => target x.val.1
  letI : Nonempty D := by
    obtain ⟨d, hd⟩ := B.finite.nonempty (V.erase p) upD oldWithin
    exact ⟨⟨d, hd⟩⟩
  letI : Nonempty (P.Carrier D W.carrier O hD hC) := by
    obtain ⟨x, hx⟩ := C.nonempty V upV within
    exact ⟨e.symm ⟨x,hx⟩⟩
  have first := B.decorations.m3 upD upZ oldWithin hZV
  have liftD : GroupActions.PrescribedLift τ target :=
    (GroupActions.prescribed_action_point_lifting τ target
      (B.finite.r_surjective upD upZ oldWithin hZV) eqTarget).mp first
  have liftC : GroupActions.PrescribedLift ρC πC := by
    dsimp only [ρC, πC, P, hC, ontoC]
    rw [stepLocalOwnerAction, stepLocalOwner_projection]
    exact W.prescribed
  have matchingM3 : Function.Surjective ρ ∧ GroupActions.FibreTransitive ρ π :=
    onto_and_kernel_nonnested ρD ρC πD πC eqD eqC τ target eqTarget
      ontoC (B.finite.r_surjective upD upZ oldWithin hZV) liftD liftC
  have equivπ : ∀ g x, π (g • x) = ρ g • π x := by
    intro g x
    exact eqTarget g.val.1 x.val.1
  have commutes : ∀ x, F.point (Q.projection x) = π (E.point x) := by
    intro x
    apply Subtype.ext
    have fst : coordinateMap S H cco (Finset.erase_subset p V) x.val =
        (e.symm x).val.1.val := by
      simpa only [e, Equiv.apply_symm_apply] using
        stepPointEquiv_fst S H cco B next upU W V upV within hp (e.symm x)
    change coordinateMap S H cco (hZV.trans (Finset.erase_subset p V)) x.val =
      coordinateMap S H cco hZV (e.symm x).val.1.val
    rw [← fst, coordinateMap_comp]
  exact actual_onto_kernel_of_commuting Q E F ρ π equivπ commutes matchingM3

/-- The source theorem's largest-new-object specialization, with an
arbitrary OLD target. The target is not assumed to contain the new owner. -/
theorem sourceStep_largest_old_m3 (upU : IsUpset U) (W : LocalFactor S H cco B next)
    (Z : Finset (Position S H cco)) (upZ : IsUpset Z) (oldZ : Z ⊆ U) :
    let C := (sourceStep S H cco B next upU W).stage
    Function.Surjective (stageQuotient S H cco C (next_insert_upset upU next) upZ
      (Finset.Subset.refl _) (oldZ.trans (Finset.subset_insert p U))).action ∧
      GroupActions.FibreTransitive (stageQuotient S H cco C (next_insert_upset upU next) upZ
        (Finset.Subset.refl _) (oldZ.trans (Finset.subset_insert p U))).action
        (C.r (next_insert_upset upU next) upZ (Finset.Subset.refl _)
          (oldZ.trans (Finset.subset_insert p U))) := by
  apply sourceStep_old_m3 S H cco B next upU W (insert p U) Z
    (next_insert_upset upU next) upZ (Finset.Subset.refl _) (Finset.mem_insert_self _ _)
  simpa only [Finset.erase_insert next.1] using oldZ

end
end CCO.Owners.Master
