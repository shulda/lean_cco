import CCO.Owners.Master.SourceNewActions
import CCO.Owners.Master.SourceOldActions

/-! The two genuinely different target branches yield M3 from the
largest new object; coherent full finite action descent gives EVERY
nested pair. Old targets have no spurious map to the new owner. -/

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

theorem sourceStep_m3 (upU : IsUpset U) (W : LocalFactor S H cco B next)
    {V Z : Finset (Position S H cco)} (upV : IsUpset V) (upZ : IsUpset Z)
    (within : V ⊆ insert p U) (hZV : Z ⊆ V) :
    let C := (sourceStep S H cco B next upU W).stage
    Function.Surjective (stageQuotient S H cco C upV upZ within hZV).action ∧
      GroupActions.FibreTransitive (stageQuotient S H cco C upV upZ within hZV).action
        (C.r upV upZ within hZV) := by
  let C := (sourceStep S H cco B next upU W).stage
  let equivA : ∀ {V W : Finset (Position S H cco)} (h : W ⊆ V)
      (g : G) (x : (exactAmbient S H cco).X V),
      (exactAmbient S H cco).r h (g • x) = g • (exactAmbient S H cco).r h x :=
    fun {_ _} h g x => coordinateMap_equivariant S H cco h g x
  apply C.nested_M3_of_largest equivA (next_insert_upset upU next) _ upV upZ within hZV
  intro Z upZ withinZ
  by_cases hpZ : p ∈ Z
  · exact sourceStep_new_m3 S H cco B next upU W (insert p U) Z
      (next_insert_upset upU next) upZ (Finset.Subset.refl _) withinZ hpZ
  · have oldZ : Z ⊆ U := (sourceStep S H cco B next upU W).old_subset withinZ hpZ
    exact sourceStep_largest_old_m3 S H cco B next upU W Z upZ oldZ

end
end CCO.Owners.Master
