import CCO.Owners.Master.SourceProduct
import CCO.Owners.Master.StepActionEquivalence

/-! The full product action with all components rewritten as the genuine
canonical stage maps and the ONE chosen local owner action. This common
identity is used separately for the largest and every new target. -/

universe v w t z
namespace CCO.Owners.Master
noncomputable section
open RawExact ExactCRT Provider Product

variable {A : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => A))
variable {G : Type t} [Group G] [MulAction G A] [Countable A]
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,v,w} S)
variable {T : Set A} {U : Finset (Position S H cco)}
variable (B : SourceStage.{v,w,t,z} S H cco T U)
variable {p : Position S H cco} (next : Next U p) (upU : IsUpset U)
variable (W : LocalFactor S H cco B next)
variable (V : Finset (Position S H cco)) (upV : IsUpset V)
variable (within : V ⊆ insert p U) (hp : p ∈ V)

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
  have E := product_action_equivalence P D C O hD hC ontoD ontoC
    (Subtype.val : (sourceStep S H cco B next upU W).stage.B V → _) e
    (stepPointEquiv_val S H cco B next upU W V upV within hp)
  dsimp only [P,D,C,O,hD,hC,ontoD,ontoC] at E
  simpa only [stepOldOwnerAction,stepLocalOwnerAction,
    stepOldOwner_projection,stepLocalOwner_projection] using E

end
end CCO.Owners.Master
