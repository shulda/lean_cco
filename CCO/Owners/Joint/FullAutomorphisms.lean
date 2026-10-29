import CCO.Owners.Joint.Geometry
import CCO.Owners.Joint.Matching
import Mathlib.Algebra.Group.Action.End

/-! Both directions of the ENTIRE finite structural automorphism group
identity. The common owner motion is unique, but no group section is chosen. -/

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

noncomputable def factorAction (i : I) := (P.factorOwnerQuotient B D hD surjD i).action
noncomputable def jointAction (i : I) := (P.jointOwnerQuotient B i).action

variable (fullB : FullOwners (P.finiteDiagram B))

/-- The literal finite projection square commutes at EVERY tuple. -/
theorem owner_coordinate (w : P.Witness B D hD) (i : I) :
    P.finiteOwn B D hD i (w.val i) =
      (P.finiteDiagram B).beta i ((P.ownerQuotient B D hD surjD fullB).projection w) :=
  (beta_owner (P.finiteDiagram B) (fun i => D i) (P.finiteOwn B D hD) fullB w i).symm

/-- Descent of every actual full W automorphism, on all factor and owner
points, supplies a matching tuple. -/
noncomputable def restriction :
    OrbitalAut G A (P.point B D hD) →*
      Matching (P.factorAction B D hD surjD) (P.jointAction B) where
  toFun f := ⟨((P.ownerQuotient B D hD surjD fullB).action f,
    fun i => (P.coordinateQuotient B D hD surjD i).action f), by
    intro i
    apply Subtype.ext
    apply Equiv.ext
    intro b
    obtain ⟨d, hd⟩ := surjD i b
    obtain ⟨w, hw⟩ := (P.coordinateQuotient B D hD surjD i).surjective d
    have hb : P.finiteOwn B D hD i (w.val i) = b := by
      change P.finiteOwn B D hD i
        ((P.coordinateQuotient B D hD surjD i).projection w) = b
      rw [hw, hd]
    rw [← hb]
    change ((P.factorOwnerQuotient B D hD surjD i).action
      ((P.coordinateQuotient B D hD surjD i).action f)).val
        (P.finiteOwn B D hD i (w.val i)) =
      ((P.jointOwnerQuotient B i).action
        ((P.ownerQuotient B D hD surjD fullB).action f)).val
          (P.finiteOwn B D hD i (w.val i))
    calc
      _ = P.finiteOwn B D hD i
          (((P.coordinateQuotient B D hD surjD i).action f).val (w.val i)) :=
        (P.factorOwnerQuotient B D hD surjD i).action_projection _ _
      _ = P.finiteOwn B D hD i ((f.val w).val i) :=
        congrArg (P.finiteOwn B D hD i)
          ((P.coordinateQuotient B D hD surjD i).action_projection f w)
      _ = (P.finiteDiagram B).beta i
          ((P.ownerQuotient B D hD surjD fullB).projection (f.val w)) :=
        P.owner_coordinate B D hD surjD fullB (f.val w) i
      _ = (P.finiteDiagram B).beta i
          (((P.ownerQuotient B D hD surjD fullB).action f).val
            ((P.ownerQuotient B D hD surjD fullB).projection w)) :=
        congrArg ((P.finiteDiagram B).beta i)
          ((P.ownerQuotient B D hD surjD fullB).action_projection f w).symm
      _ = ((P.jointOwnerQuotient B i).action
          ((P.ownerQuotient B D hD surjD fullB).action f)).val
            ((P.finiteDiagram B).beta i
              ((P.ownerQuotient B D hD surjD fullB).projection w)) :=
        ((P.jointOwnerQuotient B i).action_projection _ _).symm
      _ = _ := congrArg _ (P.owner_coordinate B D hD surjD fullB w i).symm⟩
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

/-- Every matching full-factor tuple preserves the FULL compatible carrier;
its point permutation preserves original fine colours by the proved readout. -/
noncomputable def lift :
    Matching (P.factorAction B D hD surjD) (P.jointAction B) →*
      OrbitalAut G A (P.point B D hD) := by
  letI := witnessAction (P.finiteDiagram B) fullB (P.finiteOwn B D hD)
    (P.factorAction B D hD surjD) (P.jointAction B)
    (fun i g x => ((P.factorOwnerQuotient B D hD surjD i).action_projection g x).symm)
    (fun i g x => ((P.jointOwnerQuotient B i).action_projection g x).symm)
  refine {
    toFun := fun k => ⟨MulAction.toPerm k, ?_⟩
    map_one' := ?_
    map_mul' := ?_ }
  · apply (mem_orbitalAut_iff _).mpr
    intro w v
    apply (P.fine _ _ _ _).mp
    intro i
    simp only [P.point_coordinate]
    exact orbitalAut_pair (k.val.2 i) (w.val i) (v.val i)
  · apply Subtype.ext
    exact (MulAction.toPermHom _ _).map_one
  · intro k l
    apply Subtype.ext
    exact (MulAction.toPermHom _ _).map_mul k l

@[simp] theorem lift_coordinate
    (k : Matching (P.factorAction B D hD surjD) (P.jointAction B))
    (w : P.Witness B D hD) (i : I) :
    ((P.lift B D hD surjD fullB k).val w).val i = (k.val.2 i).val (w.val i) := rfl

@[simp] theorem lift_owner
    (k : Matching (P.factorAction B D hD surjD) (P.jointAction B))
    (w : P.Witness B D hD) :
    (P.ownerQuotient B D hD surjD fullB).projection
      ((P.lift B D hD surjD fullB k).val w) =
      k.val.1.val ((P.ownerQuotient B D hD surjD fullB).projection w) := by
  exact owner_smul (P.finiteDiagram B) fullB (P.finiteOwn B D hD)
    (P.factorAction B D hD surjD) (P.jointAction B)
    (fun i g x => ((P.factorOwnerQuotient B D hD surjD i).action_projection g x).symm)
    (fun i g x => ((P.jointOwnerQuotient B i).action_projection g x).symm) k w

@[simp] theorem lift_restriction (f : OrbitalAut G A (P.point B D hD)) :
    P.lift B D hD surjD fullB (P.restriction B D hD surjD fullB f) = f := by
  apply Subtype.ext
  apply Equiv.ext
  intro w
  apply Subtype.ext
  funext i
  exact (P.coordinateQuotient B D hD surjD i).action_projection f w

@[simp] theorem ownerAction_lift
    (k : Matching (P.factorAction B D hD surjD) (P.jointAction B)) :
    (P.ownerQuotient B D hD surjD fullB).action (P.lift B D hD surjD fullB k) =
      k.val.1 := by
  apply Subtype.ext
  apply Equiv.ext
  intro b
  obtain ⟨w, rfl⟩ := (P.ownerQuotient B D hD surjD fullB).surjective b
  rw [OrbitalQuotient.action_projection, P.lift_owner]

@[simp] theorem restriction_lift
    (k : Matching (P.factorAction B D hD surjD) (P.jointAction B)) :
    P.restriction B D hD surjD fullB (P.lift B D hD surjD fullB k) = k := by
  apply Subtype.ext
  apply Prod.ext
  · exact P.ownerAction_lift B D hD surjD fullB k
  · funext i
    apply Subtype.ext
    apply Equiv.ext
    intro d
    obtain ⟨w, rfl⟩ := (P.coordinateQuotient B D hD surjD i).surjective d
    change ((P.coordinateQuotient B D hD surjD i).action
      (P.lift B D hD surjD fullB k)).val
        ((P.coordinateQuotient B D hD surjD i).projection w) = _
    rw [OrbitalQuotient.action_projection]
    exact P.lift_coordinate B D hD surjD fullB k w i

/-- C16: both directions of the actual full automorphism group identity,
including all finite owners and all named original fine colours. -/
noncomputable def fullAutEquiv :
    OrbitalAut G A (P.point B D hD) ≃*
      Matching (P.factorAction B D hD surjD) (P.jointAction B) where
  toFun := P.restriction B D hD surjD fullB
  invFun := P.lift B D hD surjD fullB
  left_inv := P.lift_restriction B D hD surjD fullB
  right_inv := P.restriction_lift B D hD surjD fullB
  map_mul' := (P.restriction B D hD surjD fullB).map_mul

/-- Complete owner-coordinate actions jointly determine EVERY full B
motion; individual coordinate action maps need not be onto. -/
theorem jointAction_injective :
    Function.Injective (fun g : OrbitalAut G Ω (Subtype.val : B → Ω) =>
      fun i => P.jointAction B i g) := by
  intro g h hgh
  apply Subtype.ext
  apply Equiv.ext
  intro b
  apply (P.finiteDiagram B).jointly_injective
  intro i
  calc
    (P.finiteDiagram B).beta i (g.val b) =
        (P.jointAction B i g).val ((P.finiteDiagram B).beta i b) :=
      ((P.jointOwnerQuotient B i).action_projection g b).symm
    _ = (P.jointAction B i h).val ((P.finiteDiagram B).beta i b) := by
      exact congrArg (fun a : OrbitalAut G (O i) (Subtype.val : P.OwnerImage B i → O i) =>
        a.val ((P.finiteDiagram B).beta i b)) (congrFun hgh i)
    _ = (P.finiteDiagram B).beta i (h.val b) :=
      (P.jointOwnerQuotient B i).action_projection h b

/-- The boxed JWA existential-coordinate presentation, with the unique
common owner component forgotten by a natural group isomorphism. -/
noncomputable def fullAutCoordinatesEquiv :
    OrbitalAut G A (P.point B D hD) ≃*
      ↥(coordinateGroup (P.factorAction B D hD surjD) (P.jointAction B)) :=
  (P.fullAutEquiv B D hD surjD fullB).trans
    (matchingCoordinatesEquiv (P.factorAction B D hD surjD) (P.jointAction B)
      (P.jointAction_injective B))

/-- Explicit uniqueness of the ENTIRE common owner component in JWA. -/
theorem common_owner_unique
    (a : ∀ i, OrbitalAut G (Q i) (Subtype.val : D i → Q i))
    (g h : OrbitalAut G Ω (Subtype.val : B → Ω))
    (hg : ∀ i, P.factorAction B D hD surjD i (a i) = P.jointAction B i g)
    (hh : ∀ i, P.factorAction B D hD surjD i (a i) = P.jointAction B i h) : g = h := by
  apply P.jointAction_injective B
  funext i
  exact (hg i).symm.trans (hh i)

end AmbientGeometry
end CCO.Owners.Joint
