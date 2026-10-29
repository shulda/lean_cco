import CCO.Owners.Master.SourceProduct
import CCO.Owners.Provider.Consumers
import CCO.Owners.Product.SparseTransport

/-! Ordinary EPPA at a new stage uses the WHOLE original input in that
quotient. The two coordinate images below are proved to be exactly its
original shadows. They are allowed to be sparse and their partial maps
need not descend from a partial map of the original real input. -/

universe v w t z
namespace CCO.Owners.Master
noncomputable section
open RawExact ExactCRT Provider Product

theorem prescribedEPPA_of_projection_eq {G₀ M N X Y : Type*}
    [Group G₀] [MulAction G₀ M] [MulAction G₀ N]
    {ι : X → M} {κ : Y → N}
    (Q R : OrbitalQuotient (G := G₀) ι κ) (h : Q.projection = R.projection)
    (a : Set X) (ep : PrescribedEPPAFor R a) : PrescribedEPPAFor Q a := by
  intro p hdom hmap δ hδ
  obtain ⟨g,hg,howner⟩ := ep p hdom hmap δ (by
    intro x
    simpa only [← h] using hδ x)
  exact ⟨g,hg,(DFunLike.congr_fun (quotientAction_eq_of_projection Q R h) g).trans howner⟩

variable {A : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => A))
variable {G : Type t} [Group G] [MulAction G A] [Countable A]
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,v,w} S)
variable {T : Set A} {U : Finset (Position S H cco)}
variable (B : SourceStage.{v,w,t,z} S H cco T U)
variable {p : Position S H cco} (next : Next U p)

/-- For any concrete presentation of the new finite carrier, a canonical
coordinate projection takes its sparse original input ONTO the exact old
input shadow. No product fullness is imposed on the input. -/
theorem step_shadow_projection_image (upU : IsUpset U) (W : LocalFactor S H cco B next)
    (V : Finset (Position S H cco)) (upV : IsUpset V)
    (within : V ⊆ insert p U)
    {J : Finset (Position S H cco)} (hJV : J ⊆ V)
    {X Y : Type*} (e : X ≃ (sourceStep S H cco B next upU W).stage.B V)
    (f : X → Y) (κ : Y → Coordinate S H cco J) (injectiveκ : Function.Injective κ)
    (commutes : ∀ x, κ (f x) = coordinateMap S H cco hJV (e x).val) :
    f '' {x | (e x).val ∈ originalShadow S H cco T V} =
      {y | κ y ∈ originalShadow S H cco T J} := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    change κ (f x) ∈ originalShadow S H cco T J
    rw [commutes]
    rw [← originalShadow_image S H cco T hJV]
    exact ⟨(e x).val,hx,rfl⟩
  · rintro ⟨a,ha,hay⟩
    let q : (sourceStep S H cco B next upU W).stage.B V :=
      ⟨coordinateProjection S H cco V a,
        sourceStep_contains S H cco B next upU W V upV within ⟨a,ha,rfl⟩⟩
    refine ⟨e.symm q,?_,?_⟩
    · change (e (e.symm q)).val ∈ originalShadow S H cco T V
      rw [e.apply_symm_apply]
      exact ⟨a,ha,rfl⟩
    · apply injectiveκ
      calc
        κ (f (e.symm q)) = coordinateMap S H cco hJV (e (e.symm q)).val := commutes _
        _ = coordinateMap S H cco hJV q.val :=
          congrArg (fun x : (sourceStep S H cco B next upU W).stage.B V =>
            coordinateMap S H cco hJV x.val) (e.apply_symm_apply q)
        _ = coordinateProjection S H cco J a := rfl
        _ = κ y := hay

theorem sourceStep_eppa (upU : IsUpset U) (W : LocalFactor S H cco B next)
    (V : Finset (Position S H cco)) (upV : IsUpset V) (within : V ⊆ insert p U) :
    EPPAFor (G := G)
      (ι := (Subtype.val : (sourceStep S H cco B next upU W).stage.B V → Coordinate S H cco V))
      {x | x.val ∈ originalShadow S H cco T V} := by
  classical
  let D := sourceStep S H cco B next upU W
  by_cases hp : p ∈ V
  · let P := stepGeometry S H cco upU next upV within hp
    let d := B.finite.B (V.erase p)
    let c := W.carrier
    let o := B.finite.B (strictUpper p)
    let hd := stepOldOwner S H cco B next upU V upV within hp
    let hc := stepLocalOwner S H cco B next upU W V upV within hp
    let sd := stepOldOwnerOnto S H cco B next upU V upV within hp
    let sc := stepLocalOwnerOnto S H cco B next upU W V upV within hp
    let e := stepPointEquiv S H cco B next upU W V upV within hp
    let a : Set (D.stage.B V) := {x | x.val ∈ originalShadow S H cco T V}
    have firstImage : (fun x : P.Carrier d c o hd hc => x.val.1) '' (e ⁻¹' a) =
        {x : d | x.val ∈ originalShadow S H cco T (V.erase p)} := by
      exact step_shadow_projection_image S H cco B next upU W V upV within
        (Finset.erase_subset p V) e (fun x => x.val.1) Subtype.val Subtype.val_injective
        (fun x => (stepPointEquiv_fst S H cco B next upU W V upV within hp x).symm)
    have secondImage : (fun x : P.Carrier d c o hd hc => x.val.2) '' (e ⁻¹' a) =
        {x : c | x.val ∈ originalShadow S H cco T (insert p (strictUpper p))} := by
      exact step_shadow_projection_image S H cco B next upU W V upV within
        (D.principal_subset upV within hp) e (fun x => x.val.2) Subtype.val
        Subtype.val_injective
        (fun x => (stepPointEquiv_snd S H cco B next upU W V upV within hp x).symm)
    apply eppa_congr e (fun x => stepPointEquiv_val S H cco B next upU W V upV within hp x) a
    apply P.eppa_full_product d c o hd hc sc sd (e ⁻¹' a)
    · rw [firstImage]
      exact B.decorations.eppa (V.erase p) (next_erase_upset upU next upV within)
        (next_erase_subset within)
    · rw [secondImage]
      apply prescribedEPPA_of_projection_eq (P.quotientOwnerC c o hc sc) W.quotient
        (stepLocalOwner_projection S H cco B next upU W V upV within hp)
      exact W.prescribed_eppa
  · have hVU := D.old_subset within hp
    rw [D.stage_old V hVU]
    exact B.decorations.eppa V upV hVU

end
end CCO.Owners.Master
