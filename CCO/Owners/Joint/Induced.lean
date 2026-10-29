import CCO.Owners.Joint.PointAction
import CCO.Owners.Product.Induced

/-! The tuple system lives on a literal induced original subset. Conjugating
by its proved carrier equivalence transports the FULL structural group,
and the actual quotient actions are proved to intertwine that transport. -/

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

@[simp] theorem pointCarrierEquiv_val (w : P.Witness B D hD) :
    (P.pointCarrierEquiv B D hD w).val = P.point B D hD w := rfl

@[simp] theorem point_symm (x : P.inducedCarrier D) :
    P.point B D hD ((P.pointCarrierEquiv B D hD).symm x) = x.val :=
  congrArg Subtype.val ((P.pointCarrierEquiv B D hD).apply_symm_apply x)

/-- Literal canonical original-coordinate projection on the induced set.
Its proof of surjectivity still uses no finite-owner fullness. -/
def inducedCoordinateQuotient (i : I) :
    OrbitalQuotient (G := G) (Subtype.val : P.inducedCarrier D → A)
      (Subtype.val : D i → Q i) where
  ambient := P.coordinate i
  equivariant := P.equiv_coordinate i
  projection x := ⟨P.coordinate i x.val, x.property i⟩
  surjective := by
    intro d
    obtain ⟨w, hw⟩ := (P.coordinateQuotient B D hD surjD i).surjective d
    refine ⟨P.pointCarrierEquiv B D hD w, ?_⟩
    apply Subtype.ext
    exact (P.point_coordinate B D hD w i).trans (congrArg Subtype.val hw)
  target_injective := Subtype.val_injective
  commutes _ := rfl

/-- The canonical joint-owner projection takes values in exactly B. Its
agreement with the ambient quotient map is proved, not a new provider. -/
noncomputable def inducedOwnerQuotient :
    OrbitalQuotient (G := G) (Subtype.val : P.inducedCarrier D → A)
      (Subtype.val : B → Ω) where
  ambient := P.joint
  equivariant := P.equiv_joint
  projection x := (P.ownerQuotient B D hD surjD fullB).projection
    ((P.pointCarrierEquiv B D hD).symm x)
  surjective := (P.ownerQuotient B D hD surjD fullB).surjective.comp
    (P.pointCarrierEquiv B D hD).symm.surjective
  target_injective := Subtype.val_injective
  commutes x := by
    change ((P.ownerQuotient B D hD surjD fullB).projection
      ((P.pointCarrierEquiv B D hD).symm x)).val = P.joint x.val
    exact (P.joint_point B D hD fullB _).symm.trans
      (congrArg P.joint (P.point_symm B D hD x))

@[simp] theorem inducedOwner_projection_equiv (w : P.Witness B D hD) :
    (P.inducedOwnerQuotient B D hD surjD fullB).projection
      (P.pointCarrierEquiv B D hD w) =
      (P.ownerQuotient B D hD surjD fullB).projection w := by
  change (P.ownerQuotient B D hD surjD fullB).projection
    ((P.pointCarrierEquiv B D hD).symm (P.pointCarrierEquiv B D hD w)) = _
  rw [Equiv.symm_apply_apply]

/-- Elementary conjugation by the literal colour-preserving carrier
identification, on the ENTIRE structural automorphism groups. -/
noncomputable def inducedAutCongr :
    OrbitalAut G A (P.point B D hD) ≃*
      OrbitalAut G A (Subtype.val : P.inducedCarrier D → A) :=
  orbitalAutCongr (P.pointCarrierEquiv B D hD) (fun _ => rfl)

@[simp] theorem inducedAutCongr_apply
    (g : OrbitalAut G A (P.point B D hD)) (w : P.Witness B D hD) :
    (P.inducedAutCongr B D hD g).val (P.pointCarrierEquiv B D hD w) =
      P.pointCarrierEquiv B D hD (g.val w) := by
  change P.pointCarrierEquiv B D hD
    (g.val ((P.pointCarrierEquiv B D hD).symm (P.pointCarrierEquiv B D hD w))) = _
  rw [Equiv.symm_apply_apply]

/-- JWA on the ACTUAL full original induced subset, with every finite
structural automorphism accounted for. -/
noncomputable def actualInducedAutEquiv :
    OrbitalAut G A (Subtype.val : P.inducedCarrier D → A) ≃*
      Matching (P.factorAction B D hD surjD) (P.jointAction B) :=
  (P.inducedAutCongr B D hD).symm.trans (P.fullAutEquiv B D hD surjD fullB)

/-- Quotient descent commutes with actual full-group conjugation; the map
on ALL finite joint owners is exactly the previously constructed action. -/
theorem inducedOwner_action_congr (g : OrbitalAut G A (P.point B D hD)) :
    (P.inducedOwnerQuotient B D hD surjD fullB).action (P.inducedAutCongr B D hD g) =
      (P.ownerQuotient B D hD surjD fullB).action g := by
  apply Subtype.ext
  apply Equiv.ext
  intro b
  obtain ⟨w, rfl⟩ := (P.ownerQuotient B D hD surjD fullB).surjective b
  calc
    _ = ((P.inducedOwnerQuotient B D hD surjD fullB).action
        (P.inducedAutCongr B D hD g)).val
          ((P.inducedOwnerQuotient B D hD surjD fullB).projection
            (P.pointCarrierEquiv B D hD w)) :=
      congrArg _ (P.inducedOwner_projection_equiv B D hD surjD fullB w).symm
    _ = (P.inducedOwnerQuotient B D hD surjD fullB).projection
        ((P.inducedAutCongr B D hD g).val (P.pointCarrierEquiv B D hD w)) :=
      (P.inducedOwnerQuotient B D hD surjD fullB).action_projection _ _
    _ = (P.inducedOwnerQuotient B D hD surjD fullB).projection
        (P.pointCarrierEquiv B D hD (g.val w)) :=
      congrArg _ (P.inducedAutCongr_apply B D hD g w)
    _ = (P.ownerQuotient B D hD surjD fullB).projection (g.val w) :=
      P.inducedOwner_projection_equiv B D hD surjD fullB (g.val w)
    _ = _ := ((P.ownerQuotient B D hD surjD fullB).action_projection g w).symm

/-- Point motion transported by the actual induced carrier equivalence. -/
theorem inducedAutCongr_moves
    (g : OrbitalAut G A (P.point B D hD)) (x y : P.inducedCarrier D)
    (h : g.val ((P.pointCarrierEquiv B D hD).symm x) =
      (P.pointCarrierEquiv B D hD).symm y) : (P.inducedAutCongr B D hD g).val x = y := by
  calc
    _ = (P.inducedAutCongr B D hD g).val
        (P.pointCarrierEquiv B D hD ((P.pointCarrierEquiv B D hD).symm x)) :=
      congrArg _ ((P.pointCarrierEquiv B D hD).apply_symm_apply x).symm
    _ = P.pointCarrierEquiv B D hD (g.val ((P.pointCarrierEquiv B D hD).symm x)) :=
      P.inducedAutCongr_apply B D hD g _
    _ = P.pointCarrierEquiv B D hD ((P.pointCarrierEquiv B D hD).symm y) := congrArg _ h
    _ = y := (P.pointCarrierEquiv B D hD).apply_symm_apply y

/-- Every prescribed point motion acts on the literal original induced
subset and induces the specified action on ALL of the finite owner set. -/
theorem actual_prescribed_point
    (factorLift : ∀ i, GroupActions.PrescribedLift
      (P.factorAction B D hD surjD i) (P.finiteOwn B D hD i)) :
    GroupActions.PrescribedLift (P.inducedOwnerQuotient B D hD surjD fullB).action
      (P.inducedOwnerQuotient B D hD surjD fullB).projection := by
  intro x y γ hγ
  obtain ⟨g, hg, hmove⟩ := P.prescribed_point B D hD surjD fullB factorLift
    ((P.pointCarrierEquiv B D hD).symm x) ((P.pointCarrierEquiv B D hD).symm y) γ hγ
  exact ⟨P.inducedAutCongr B D hD g,
    (P.inducedOwner_action_congr B D hD surjD fullB g).trans hg,
    P.inducedAutCongr_moves B D hD g x y hmove⟩

/-- Onto full owner action and fibre-transitive kernel on the actual
original induced carrier, including the already discharged empty branch. -/
theorem actual_onto_and_kernel
    (factorLift : ∀ i, GroupActions.PrescribedLift
      (P.factorAction B D hD surjD i) (P.finiteOwn B D hD i)) :
    Function.Surjective (P.inducedOwnerQuotient B D hD surjD fullB).action ∧
      GroupActions.FibreTransitive (P.inducedOwnerQuotient B D hD surjD fullB).action
        (P.inducedOwnerQuotient B D hD surjD fullB).projection := by
  obtain ⟨onto, fibre⟩ := P.onto_and_kernel B D hD surjD fullB factorLift
  constructor
  · intro γ
    obtain ⟨g, hg⟩ := onto γ
    exact ⟨P.inducedAutCongr B D hD g,
      (P.inducedOwner_action_congr B D hD surjD fullB g).trans hg⟩
  · intro x y hxy
    obtain ⟨g, hg, hmove⟩ := fibre
      ((P.pointCarrierEquiv B D hD).symm x) ((P.pointCarrierEquiv B D hD).symm y) hxy
    exact ⟨P.inducedAutCongr B D hD g,
      (P.inducedOwner_action_congr B D hD surjD fullB g).trans hg,
      P.inducedAutCongr_moves B D hD g x y hmove⟩

end AmbientGeometry
end CCO.Owners.Joint
