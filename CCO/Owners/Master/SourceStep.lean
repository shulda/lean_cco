import CCO.Owners.Master.StageData

/-! One ACTUAL provider call supplies a full local factor. The canonical
binary square then constructs every new finite quotient subset together,
preserving the SAME old diagram and every original projected input. -/

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

def localInput_over (x : originalShadow S H cco T (insert p (strictUpper p))) :
    coordinateMap S H cco (Finset.subset_insert p (strictUpper p)) x.val ∈
      B.finite.B (strictUpper p) := by
  apply B.decorations.contains (strictUpper p) (strictUpper_upset p)
    (next_strictUpper_subset next)
  rw [← originalShadow_image S H cco T (Finset.subset_insert p (strictUpper p))]
  exact ⟨x.val,x.property,rfl⟩

abbrev LocalFactor :=
  OwnerWitness
    (quotientSource S H cco (coordinateKernel S H cco (insert p (strictUpper p))))
    (quotientSource_homogeneous S H cco (coordinateKernel S H cco (insert p (strictUpper p))))
    (coordinateMap S H cco (Finset.subset_insert p (strictUpper p)))
    (coordinateMap_equivariant S H cco (Finset.subset_insert p (strictUpper p)))
    (B.finite.B (strictUpper p))
    (originalShadow S H cco T (insert p (strictUpper p)))
    (localInput_over S H cco B next)

/-- This is the sole source-provider invocation at a stage. Its ordinary
EPPA input may be EPPA of the ORIGINAL source when the principal upset is
the whole poset; identity is therefore explicitly present in `ep`. -/
theorem exists_localFactor (finiteT : T.Finite)
    (ep : AllQuotientsEPPA S H cco) :
    Nonempty (LocalFactor S H cco B next) := by
  exact relative_owner_provider S H cco _ _
    (coordinateKernel_antitone S H cco (Finset.subset_insert p (strictUpper p)))
    (ep _) (B.finite.B (strictUpper p))
    (B.finite.finite _ (strictUpper_upset p) (next_strictUpper_subset next))
    (B.finite.nonempty _ (strictUpper_upset p) (next_strictUpper_subset next))
    (B.decorations.closed _ (strictUpper_upset p) (next_strictUpper_subset next))
    (originalShadow S H cco T (insert p (strictUpper p)))
    (finiteT.image _) (localInput_over S H cco B next)

def sourceStep (upU : IsUpset U) (W : LocalFactor S H cco B next) :
    Diagram.Step B.finite p (strictUpper p) where
  fresh := next.1
  owner_subset := next_strictUpper_subset next
  valid_owner := strictUpper_upset p
  valid_erase V hV within := next_erase_upset upU next hV within
  owner_erase V hV _ hp := next_strictUpper_subset_erase hV hp
  localSet := W.carrier
  local_finite := W.finite
  local_over x hx := W.over ⟨x,hx⟩
  local_onto b hb := by
    obtain ⟨x,hx⟩ := W.onto ⟨b,hb⟩
    exact ⟨x.val,x.property,congrArg Subtype.val hx⟩
  glue V hV within hp b x owner := step_glue S H cco upU next hV within hp b x owner

theorem sourceStep_contains (upU : IsUpset U) (W : LocalFactor S H cco B next)
    (V : Finset (Position S H cco)) (upV : IsUpset V) (within : V ⊆ insert p U) :
    originalShadow S H cco T V ⊆ (sourceStep S H cco B next upU W).stage.B V := by
  let D := sourceStep S H cco B next upU W
  intro x hx
  by_cases hp : p ∈ V
  · apply (D.mem_new_new hp (D.principal_subset upV within hp) x).mpr
    constructor
    · apply B.decorations.contains (V.erase p) (next_erase_upset upU next upV within)
        (next_erase_subset within)
      rw [← originalShadow_image S H cco T (Finset.erase_subset p V)]
      exact ⟨x,hx,rfl⟩
    · apply W.contains
      rw [← originalShadow_image S H cco T (D.principal_subset upV within hp)]
      exact ⟨x,hx,rfl⟩
  · apply (D.mem_new_old hp x).mpr
    exact B.decorations.contains V upV (D.old_subset within hp) hx

end
end CCO.Owners.Master
