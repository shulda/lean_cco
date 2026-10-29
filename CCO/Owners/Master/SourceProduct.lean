import CCO.Owners.Master.SourceStep
import CCO.Owners.Product.Induced

/-! Canonical finite product data shared by the full-group and sparse
EPPA steps. Every map is the actual original quotient projection. -/

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

theorem quotientAction_eq_of_projection {G₀ M N X Y : Type*}
    [Group G₀] [MulAction G₀ M] [MulAction G₀ N]
    {ι : X → M} {κ : Y → N}
    (Q R : OrbitalQuotient (G := G₀) ι κ) (h : Q.projection = R.projection) :
    Q.action = R.action := by
  apply MonoidHom.ext
  intro g
  apply Subtype.ext
  apply Equiv.ext
  intro y
  obtain ⟨x,rfl⟩ := Q.surjective y
  calc
    _ = Q.projection (g.val x) := Q.action_projection g x
    _ = R.projection (g.val x) := congrFun h _
    _ = (R.action g).val (R.projection x) := (R.action_projection g x).symm
    _ = _ := congrArg (R.action g).val (congrFun h x).symm

def stepOldOwner (upU : IsUpset U) (V : Finset (Position S H cco))
    (upV : IsUpset V) (within : V ⊆ insert p U) (hp : p ∈ V)
    (x : B.finite.B (V.erase p)) :
    (stepGeometry S H cco upU next upV within hp).rD x.val ∈
      B.finite.B (strictUpper p) := by
  rw [stepGeometry_rD]
  exact B.finite.mapsTo (next_erase_upset upU next upV within) (strictUpper_upset p)
    (next_erase_subset within) (next_strictUpper_subset_erase upV hp) x.val x.property

def stepLocalOwner (upU : IsUpset U) (W : LocalFactor S H cco B next)
    (V : Finset (Position S H cco)) (upV : IsUpset V)
    (within : V ⊆ insert p U) (hp : p ∈ V) (x : W.carrier) :
    (stepGeometry S H cco upU next upV within hp).rC x.val ∈
      B.finite.B (strictUpper p) := by
  rw [stepGeometry_rC]
  exact W.over x

theorem stepOldOwnerOnto (upU : IsUpset U) (V : Finset (Position S H cco))
    (upV : IsUpset V) (within : V ⊆ insert p U) (hp : p ∈ V) :
    Function.Surjective ((stepGeometry S H cco upU next upV within hp).ownerD
      (B.finite.B (V.erase p)) (B.finite.B (strictUpper p))
      (stepOldOwner S H cco B next upU V upV within hp)) := by
  intro b
  obtain ⟨x,hx⟩ := B.finite.r_surjective (next_erase_upset upU next upV within)
    (strictUpper_upset p) (next_erase_subset within) (next_strictUpper_subset_erase upV hp) b
  refine ⟨x,Subtype.ext ?_⟩
  exact (stepGeometry_rD S H cco upU next upV within hp x.val).trans
    (congrArg Subtype.val hx)

theorem stepLocalOwnerOnto (upU : IsUpset U) (W : LocalFactor S H cco B next)
    (V : Finset (Position S H cco)) (upV : IsUpset V)
    (within : V ⊆ insert p U) (hp : p ∈ V) :
    Function.Surjective ((stepGeometry S H cco upU next upV within hp).ownerC
      W.carrier (B.finite.B (strictUpper p))
      (stepLocalOwner S H cco B next upU W V upV within hp)) := by
  intro b
  obtain ⟨x,hx⟩ := W.onto b
  refine ⟨x,Subtype.ext ?_⟩
  exact (stepGeometry_rC S H cco upU next upV within hp x.val).trans
    (congrArg Subtype.val hx)

theorem stepOldOwner_projection (upU : IsUpset U) (V : Finset (Position S H cco))
    (upV : IsUpset V) (within : V ⊆ insert p U) (hp : p ∈ V) :
    (stepGeometry S H cco upU next upV within hp).ownerD
      (B.finite.B (V.erase p)) (B.finite.B (strictUpper p))
      (stepOldOwner S H cco B next upU V upV within hp) =
    (stageQuotient S H cco B.finite (next_erase_upset upU next upV within)
      (strictUpper_upset p) (next_erase_subset within)
      (next_strictUpper_subset_erase upV hp)).projection := by
  funext x
  apply Subtype.ext
  exact stepGeometry_rD S H cco upU next upV within hp x.val

theorem stepLocalOwner_projection (upU : IsUpset U) (W : LocalFactor S H cco B next)
    (V : Finset (Position S H cco)) (upV : IsUpset V)
    (within : V ⊆ insert p U) (hp : p ∈ V) :
    (stepGeometry S H cco upU next upV within hp).ownerC W.carrier
      (B.finite.B (strictUpper p)) (stepLocalOwner S H cco B next upU W V upV within hp) =
      W.quotient.projection := by
  funext x
  apply Subtype.ext
  exact stepGeometry_rC S H cco upU next upV within hp x.val

theorem stepOldOwnerAction (upU : IsUpset U) (V : Finset (Position S H cco))
    (upV : IsUpset V) (within : V ⊆ insert p U) (hp : p ∈ V) :
    (stepGeometry S H cco upU next upV within hp).ownerActionD
      (B.finite.B (V.erase p)) (B.finite.B (strictUpper p))
      (stepOldOwner S H cco B next upU V upV within hp)
      (stepOldOwnerOnto S H cco B next upU V upV within hp) =
    (stageQuotient S H cco B.finite (next_erase_upset upU next upV within)
      (strictUpper_upset p) (next_erase_subset within)
      (next_strictUpper_subset_erase upV hp)).action := by
  apply quotientAction_eq_of_projection
  exact stepOldOwner_projection S H cco B next upU V upV within hp

theorem stepLocalOwnerAction (upU : IsUpset U) (W : LocalFactor S H cco B next)
    (V : Finset (Position S H cco)) (upV : IsUpset V)
    (within : V ⊆ insert p U) (hp : p ∈ V) :
    (stepGeometry S H cco upU next upV within hp).ownerActionC W.carrier
      (B.finite.B (strictUpper p)) (stepLocalOwner S H cco B next upU W V upV within hp)
      (stepLocalOwnerOnto S H cco B next upU W V upV within hp) = W.quotient.action := by
  apply quotientAction_eq_of_projection
  exact stepLocalOwner_projection S H cco B next upU W V upV within hp

theorem stepCarrierEq (upU : IsUpset U) (W : LocalFactor S H cco B next)
    (V : Finset (Position S H cco)) (upV : IsUpset V)
    (within : V ⊆ insert p U) (hp : p ∈ V) :
    (sourceStep S H cco B next upU W).stage.B V =
      (stepGeometry S H cco upU next upV within hp).inducedCarrier
        (B.finite.B (V.erase p)) W.carrier := by
  let D := sourceStep S H cco B next upU W
  ext x
  rw [show x ∈ D.stage.B V ↔ _ from
    D.mem_new_new hp (D.principal_subset upV within hp) x]
  simp only [ProductGeometry.inducedCarrier,Set.mem_setOf_eq,
    stepGeometry_pD,stepGeometry_pC]
  rfl

def stepPointEquiv (upU : IsUpset U) (W : LocalFactor S H cco B next)
    (V : Finset (Position S H cco)) (upV : IsUpset V)
    (within : V ⊆ insert p U) (hp : p ∈ V) :
    (stepGeometry S H cco upU next upV within hp).Carrier
      (B.finite.B (V.erase p)) W.carrier (B.finite.B (strictUpper p))
      (stepOldOwner S H cco B next upU V upV within hp)
      (stepLocalOwner S H cco B next upU W V upV within hp) ≃
        (sourceStep S H cco B next upU W).stage.B V :=
  ((stepGeometry S H cco upU next upV within hp).pointCarrierEquiv
    (B.finite.B (V.erase p)) W.carrier (B.finite.B (strictUpper p))
    (stepOldOwner S H cco B next upU V upV within hp)
    (stepLocalOwner S H cco B next upU W V upV within hp)).trans
    (Set.equivOfEq (stepCarrierEq S H cco B next upU W V upV within hp).symm)

@[simp] theorem stepPointEquiv_val (upU : IsUpset U) (W : LocalFactor S H cco B next)
    (V : Finset (Position S H cco)) (upV : IsUpset V)
    (within : V ⊆ insert p U) (hp : p ∈ V)
    (x : (stepGeometry S H cco upU next upV within hp).Carrier
      (B.finite.B (V.erase p)) W.carrier (B.finite.B (strictUpper p))
      (stepOldOwner S H cco B next upU V upV within hp)
      (stepLocalOwner S H cco B next upU W V upV within hp)) :
    (stepPointEquiv S H cco B next upU W V upV within hp x).val =
      (stepGeometry S H cco upU next upV within hp).point
        (B.finite.B (V.erase p)) W.carrier (B.finite.B (strictUpper p))
        (stepOldOwner S H cco B next upU V upV within hp)
        (stepLocalOwner S H cco B next upU W V upV within hp) x := rfl

@[simp] theorem stepPointEquiv_fst (upU : IsUpset U) (W : LocalFactor S H cco B next)
    (V : Finset (Position S H cco)) (upV : IsUpset V)
    (within : V ⊆ insert p U) (hp : p ∈ V)
    (x : (stepGeometry S H cco upU next upV within hp).Carrier
      (B.finite.B (V.erase p)) W.carrier (B.finite.B (strictUpper p))
      (stepOldOwner S H cco B next upU V upV within hp)
      (stepLocalOwner S H cco B next upU W V upV within hp)) :
    coordinateMap S H cco (Finset.erase_subset p V)
      (stepPointEquiv S H cco B next upU W V upV within hp x).val = x.val.1.val := by
  rw [stepPointEquiv_val]
  exact (stepGeometry_pD S H cco upU next upV within hp _).symm.trans
    ((stepGeometry S H cco upU next upV within hp).pD_point _ _ _ _ _ x)

@[simp] theorem stepPointEquiv_snd (upU : IsUpset U) (W : LocalFactor S H cco B next)
    (V : Finset (Position S H cco)) (upV : IsUpset V)
    (within : V ⊆ insert p U) (hp : p ∈ V)
    (x : (stepGeometry S H cco upU next upV within hp).Carrier
      (B.finite.B (V.erase p)) W.carrier (B.finite.B (strictUpper p))
      (stepOldOwner S H cco B next upU V upV within hp)
      (stepLocalOwner S H cco B next upU W V upV within hp)) :
    coordinateMap S H cco
      ((sourceStep S H cco B next upU W).principal_subset upV within hp)
      (stepPointEquiv S H cco B next upU W V upV within hp x).val = x.val.2.val := by
  rw [stepPointEquiv_val]
  exact (stepGeometry_pC S H cco upU next upV within hp _).symm.trans
    ((stepGeometry S H cco upU next upV within hp).pC_point _ _ _ _ _ x)

end
end CCO.Owners.Master
