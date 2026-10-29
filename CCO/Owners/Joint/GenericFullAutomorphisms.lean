import CCO.Owners.Joint.GenericGeometry
import Mathlib.Algebra.Group.Action.End

/-! Full JWA for genuine recognized unary/binary structures. No ambient
orbital action, homogeneity, finiteness, section or extension provider is
assumed in the automorphism group identity. -/

namespace CCO.Owners.Joint.Relational.LanguageDiagram

variable {I B : Type*} {Bi Di : I → Type*}
variable {d : OwnerDiagram I B Bi} {full : FullOwners d} {π : ∀ i, Di i → Bi i}
variable (L : LanguageDiagram d full π)

noncomputable def restriction :
    L.witnessStructure.Aut →* Matching L.factorAction L.jointAction where
  toFun f := ⟨(L.toOwner.action f, fun i => (L.toFactor i).action f), by
    intro i
    apply Subtype.ext
    apply Equiv.ext
    intro b
    obtain ⟨x, hx⟩ := (L.factorOwner i).surjective b
    have hx' : π i x = b := by simpa only [L.factorOwner_projection] using hx
    obtain ⟨w, hw⟩ := (L.toFactor i).surjective x
    have hw' : w.val i = x := by simpa only [L.toFactor_projection] using hw
    rw [← hx', ← hw']
    calc
      (L.factorAction i ((L.toFactor i).action f)).val (π i (w.val i)) =
          π i (((L.toFactor i).action f).val (w.val i)) := L.factor_action i _ _
      _ = π i ((f.val w).val i) := congrArg (π i) (L.coordinate_action i f w)
      _ = d.beta i (owner d Di π full (f.val w)) :=
        (beta_owner d Di π full (f.val w) i).symm
      _ = d.beta i ((L.toOwner.action f).val (owner d Di π full w)) :=
        congrArg (d.beta i) (L.owner_action f w).symm
      _ = (L.jointAction i (L.toOwner.action f)).val (d.beta i (owner d Di π full w)) :=
        (L.joint_action i _ _).symm
      _ = (L.jointAction i (L.toOwner.action f)).val (π i (w.val i)) :=
        congrArg _ (beta_owner d Di π full w i)⟩
  map_one' := by
    apply Subtype.ext
    apply Prod.ext
    · exact map_one _
    · funext i; exact map_one _
  map_mul' f g := by
    apply Subtype.ext
    apply Prod.ext
    · exact map_mul _ _ _
    · funext i; exact map_mul _ _ _

/-- Fine readout checks ALL original unary and binary relations. -/
noncomputable def lift :
    Matching L.factorAction L.jointAction →* L.witnessStructure.Aut := by
  letI := witnessAction d full π L.factorAction L.jointAction
    (fun i g x => (L.factor_action i g x).symm)
    (fun i g b => (L.joint_action i g b).symm)
  refine {
    toFun := fun k => ⟨MulAction.toPerm k, ?_⟩
    map_one' := ?_
    map_mul' := ?_ }
  · apply samePair_mem_aut
    intro w v
    apply L.fine w v
    intro i
    exact aut_pair (k.val.2 i) (w.val i) (v.val i)
  · apply Subtype.ext
    exact (MulAction.toPermHom _ _).map_one
  · intro k l
    apply Subtype.ext
    exact (MulAction.toPermHom _ _).map_mul k l

@[simp] theorem lift_coordinate (k : Matching L.factorAction L.jointAction)
    (w : Carrier d Di π) (i : I) :
    ((L.lift k).val w).val i = (k.val.2 i).val (w.val i) := rfl

@[simp] theorem lift_owner (k : Matching L.factorAction L.jointAction)
    (w : Carrier d Di π) :
    L.toOwner.projection ((L.lift k).val w) = k.val.1.val (L.toOwner.projection w) := by
  letI := witnessAction d full π L.factorAction L.jointAction
    (fun i g x => (L.factor_action i g x).symm)
    (fun i g b => (L.joint_action i g b).symm)
  simp only [L.toOwner_projection]
  change owner d Di π full (k • w) = k.val.1 • owner d Di π full w
  exact owner_smul d full π L.factorAction L.jointAction
    (fun i g x => (L.factor_action i g x).symm)
    (fun i g b => (L.joint_action i g b).symm) k w

@[simp] theorem lift_restriction (f : L.witnessStructure.Aut) :
    L.lift (L.restriction f) = f := by
  apply Subtype.ext
  apply Equiv.ext
  intro w
  apply Subtype.ext
  funext i
  exact L.coordinate_action i f w

@[simp] theorem ownerAction_lift (k : Matching L.factorAction L.jointAction) :
    L.toOwner.action (L.lift k) = k.val.1 := by
  apply Subtype.ext
  apply Equiv.ext
  intro b
  obtain ⟨w, rfl⟩ := L.toOwner.surjective b
  rw [RecognizableQuotient.action_projection, L.lift_owner]

@[simp] theorem restriction_lift (k : Matching L.factorAction L.jointAction) :
    L.restriction (L.lift k) = k := by
  apply Subtype.ext
  apply Prod.ext
  · exact L.ownerAction_lift k
  · funext i
    apply Subtype.ext
    apply Equiv.ext
    intro x
    obtain ⟨w, rfl⟩ := (L.toFactor i).surjective x
    change ((L.toFactor i).action (L.lift k)).val ((L.toFactor i).projection w) = _
    rw [RecognizableQuotient.action_projection]
    simpa only [L.toFactor_projection] using L.lift_coordinate k w i

/-- Both directions and group laws concern the ENTIRE structural groups. -/
noncomputable def fullAutEquiv :
    L.witnessStructure.Aut ≃* Matching L.factorAction L.jointAction where
  toFun := L.restriction
  invFun := L.lift
  left_inv := L.lift_restriction
  right_inv := L.restriction_lift
  map_mul' := L.restriction.map_mul

theorem jointAction_injective :
    Function.Injective (fun g : L.ownerStructure.Aut => fun i => L.jointAction i g) := by
  intro g h hgh
  apply Subtype.ext
  apply Equiv.ext
  intro b
  apply d.jointly_injective
  intro i
  calc
    d.beta i (g.val b) = (L.jointAction i g).val (d.beta i b) :=
      (L.joint_action i g b).symm
    _ = (L.jointAction i h).val (d.beta i b) :=
      congrArg (fun a : (L.ownerCoordinateStructure i).Aut => a.val (d.beta i b))
        (congrFun hgh i)
    _ = d.beta i (h.val b) := L.joint_action i h b

noncomputable def fullAutCoordinatesEquiv :
    L.witnessStructure.Aut ≃* ↥(coordinateGroup L.factorAction L.jointAction) :=
  L.fullAutEquiv.trans
    (matchingCoordinatesEquiv L.factorAction L.jointAction L.jointAction_injective)

theorem common_owner_unique (a : ∀ i, (L.factorStructure i).Aut)
    (g h : L.ownerStructure.Aut)
    (hg : ∀ i, L.factorAction i (a i) = L.jointAction i g)
    (hh : ∀ i, L.factorAction i (a i) = L.jointAction i h) : g = h := by
  apply L.jointAction_injective
  funext i
  exact (hg i).symm.trans (hh i)

end CCO.Owners.Joint.Relational.LanguageDiagram
