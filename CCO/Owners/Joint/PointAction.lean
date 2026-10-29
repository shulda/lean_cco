import CCO.Owners.Joint.FullAutomorphisms

/-! Every prescribed ENTIRE joint-owner action lifts on points. The onto
and fibre-kernel conclusion handles empty finite owner systems directly,
before invoking the shared criterion on a nonempty domain. -/

namespace CCO.Owners.Joint
open CCO.Owners.Product

variable {G I A Ω : Type*} {Q O : I → Type*}
variable [Group G] [MulAction G A] [MulAction G Ω]
variable [∀ i, MulAction G (Q i)] [∀ i, MulAction G (O i)]

namespace AmbientGeometry
variable (P : AmbientGeometry (G := G) (I := I) (A := A) (Ω := Ω) (Q := Q) (O := O))
variable (B : Set Ω) (D : ∀ i, Set (Q i))
variable (hD : ∀ i (d : D i), P.own i d.val ∈ P.OwnerImage B i)
variable (surjD : ∀ i, Function.Surjective (P.finiteOwn B D hD i))
variable (fullB : FullOwners (P.finiteDiagram B))

/-- C17: one SAME joint-owner action is used in every coordinate and is
retained on ALL B after lifting through the full finite group identity. -/
theorem prescribed_point
    (factorLift : ∀ i, GroupActions.PrescribedLift
      (P.factorAction B D hD surjD i) (P.finiteOwn B D hD i)) :
    GroupActions.PrescribedLift (P.ownerQuotient B D hD surjD fullB).action
      (P.ownerQuotient B D hD surjD fullB).projection := by
  letI := witnessAction (P.finiteDiagram B) fullB (P.finiteOwn B D hD)
    (P.factorAction B D hD surjD) (P.jointAction B)
    (fun i g x => ((P.factorOwnerQuotient B D hD surjD i).action_projection g x).symm)
    (fun i g x => ((P.jointOwnerQuotient B i).action_projection g x).symm)
  intro x y γ hγ
  obtain ⟨k, hk, hmove⟩ := matching_prescribed (P.finiteDiagram B) fullB
    (P.finiteOwn B D hD) (P.factorAction B D hD surjD) (P.jointAction B)
    (fun i g x => ((P.factorOwnerQuotient B D hD surjD i).action_projection g x).symm)
    (fun i g x => ((P.jointOwnerQuotient B i).action_projection g x).symm)
    factorLift x y γ hγ
  refine ⟨P.lift B D hD surjD fullB k, ?_, ?_⟩
  · exact (P.ownerAction_lift B D hD surjD fullB k).trans hk
  · exact hmove

/-- An empty actual owner set has the trivial FULL induced owner group. -/
theorem empty_owner_aut_subsingleton [IsEmpty B] :
    Subsingleton (OrbitalAut G Ω (Subtype.val : B → Ω)) := inferInstance

include fullB in
/-- The onto owner map already proves emptiness of W from emptiness of B;
no point-action criterion or factor-lift hypothesis is invoked. -/
theorem empty_witness [IsEmpty B] : IsEmpty (P.Witness B D hD) :=
  ⟨fun w => isEmptyElim (owner (P.finiteDiagram B) (fun i => D i)
    (P.finiteOwn B D hD) fullB w)⟩

include fullB in
/-- The FULL finite W group is trivial in the empty branch. -/
theorem empty_witness_aut_subsingleton [IsEmpty B] :
    Subsingleton (OrbitalAut G A (P.point B D hD)) := by
  letI := P.empty_witness B D hD fullB
  infer_instance

include fullB in
/-- All factor groups and their full matching subgroup are trivial when
the owner is empty; this is not the vacuous prescribed-point criterion. -/
theorem empty_matching_subsingleton [IsEmpty B] :
    Subsingleton (Matching (P.factorAction B D hD surjD) (P.jointAction B)) := by
  letI := P.empty_witness_aut_subsingleton B D hD fullB
  exact (P.fullAutEquiv B D hD surjD fullB).symm.injective.subsingleton

/-- C18: empty systems are discharged directly. Only the nonempty branch
uses the shared equivariant onto-map point criterion. No individual rho_i
surjectivity, section, or source EPPA hypothesis is present. -/
theorem onto_and_kernel
    (factorLift : ∀ i, GroupActions.PrescribedLift
      (P.factorAction B D hD surjD i) (P.finiteOwn B D hD i)) :
    Function.Surjective (P.ownerQuotient B D hD surjD fullB).action ∧
      GroupActions.FibreTransitive (P.ownerQuotient B D hD surjD fullB).action
        (P.ownerQuotient B D hD surjD fullB).projection := by
  classical
  by_cases inhabited : Nonempty B
  · letI := inhabited
    letI : Nonempty (P.Witness B D hD) := by
      obtain ⟨b⟩ := inhabited
      obtain ⟨w, _⟩ := (P.ownerQuotient B D hD surjD fullB).surjective b
      exact ⟨w⟩
    apply (GroupActions.prescribed_action_point_lifting _ _
      (P.ownerQuotient B D hD surjD fullB).surjective
      (fun g w => ((P.ownerQuotient B D hD surjD fullB).action_projection g w).symm)).mpr
    exact P.prescribed_point B D hD surjD fullB factorLift
  · letI : IsEmpty B := not_nonempty_iff.mp inhabited
    letI := empty_owner_aut_subsingleton (G := G) B
    letI := P.empty_witness B D hD fullB
    constructor
    · intro γ
      exact ⟨1, Subsingleton.elim _ _⟩
    · intro x
      exact isEmptyElim x

include fullB in
/-- Empty original inputs extend by the identity in the empty full W.
This direct boundary clause needs no ordinary EPPA provider. -/
theorem empty_eppa [IsEmpty B] (a : Set (P.Witness B D hD)) :
    EPPAFor (G := G) (ι := P.point B D hD) a := by
  letI := P.empty_witness B D hD fullB
  intro p _ _
  refine ⟨1, ?_⟩
  intro x
  exact isEmptyElim x.val

end AmbientGeometry
end CCO.Owners.Joint
