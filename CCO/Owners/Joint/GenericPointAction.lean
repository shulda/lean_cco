import CCO.Owners.Joint.GenericFullAutomorphisms

/-! Prescribed entire owner actions and the fibre-kernel conclusion for
genuine recognized binary structures, including direct empty branches. -/

namespace CCO.Owners.Joint.Relational.LanguageDiagram

variable {I B : Type*} {Bi Di : I → Type*}
variable {d : OwnerDiagram I B Bi} {full : FullOwners d} {π : ∀ i, Di i → Bi i}
variable (L : LanguageDiagram d full π)

theorem prescribed_point
    (factorLift : ∀ i, GroupActions.PrescribedLift (L.factorAction i) (π i)) :
    GroupActions.PrescribedLift L.toOwner.action L.toOwner.projection := by
  letI := witnessAction d full π L.factorAction L.jointAction
    (fun i g x => (L.factor_action i g x).symm)
    (fun i g b => (L.joint_action i g b).symm)
  intro x y γ hγ
  have hγ' : γ • owner d Di π full x = owner d Di π full y := by
    simpa only [L.toOwner_projection] using hγ
  obtain ⟨k, hk, hmove⟩ := matching_prescribed d full π L.factorAction L.jointAction
    (fun i g x => (L.factor_action i g x).symm)
    (fun i g b => (L.joint_action i g b).symm) factorLift x y γ hγ'
  exact ⟨L.lift k, (L.ownerAction_lift k).trans hk, hmove⟩

theorem empty_owner_aut_subsingleton [IsEmpty B] : Subsingleton L.ownerStructure.Aut :=
  inferInstance

include L in
/-- Actual owner projection excludes every tuple if the owner is empty. -/
theorem empty_witness [IsEmpty B] : IsEmpty (Carrier d Di π) :=
  ⟨fun w => isEmptyElim (L.toOwner.projection w)⟩

theorem empty_witness_aut_subsingleton [IsEmpty B] :
    Subsingleton L.witnessStructure.Aut := by
  letI := L.empty_witness
  infer_instance

theorem empty_matching_subsingleton [IsEmpty B] :
    Subsingleton (Matching L.factorAction L.jointAction) := by
  letI := L.empty_witness_aut_subsingleton
  exact L.fullAutEquiv.symm.injective.subsingleton

/-- Empty point conditions alone do not imply onto group maps. Here the
empty owner's FULL structural automorphism group is proved trivial first. -/
theorem onto_and_kernel
    (factorLift : ∀ i, GroupActions.PrescribedLift (L.factorAction i) (π i)) :
    Function.Surjective L.toOwner.action ∧
      GroupActions.FibreTransitive L.toOwner.action L.toOwner.projection := by
  classical
  by_cases inhabited : Nonempty B
  · letI := inhabited
    letI : Nonempty (Carrier d Di π) := by
      obtain ⟨b⟩ := inhabited
      obtain ⟨w, _⟩ := L.toOwner.surjective b
      exact ⟨w⟩
    apply (GroupActions.prescribed_action_point_lifting _ _ L.toOwner.surjective
      (fun g w => (L.toOwner.action_projection g w).symm)).mpr
    exact L.prescribed_point factorLift
  · letI : IsEmpty B := not_nonempty_iff.mp inhabited
    letI := L.empty_owner_aut_subsingleton
    letI := L.empty_witness
    constructor
    · intro γ
      exact ⟨1, Subsingleton.elim _ _⟩
    · intro x
      exact isEmptyElim x

/-- The empty original input uses the identity, with no EPPA premise. -/
theorem empty_eppa [IsEmpty B] (a : Set (Carrier d Di π)) :
    EPPAFor L.witnessStructure a := by
  letI := L.empty_witness
  intro p _ _
  exact ⟨1, fun x => isEmptyElim x.val⟩

end CCO.Owners.Joint.Relational.LanguageDiagram
