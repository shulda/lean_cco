import CCO.Owners.Joint.Carrier
import CCO.Owners.Product.SparseDescent

/-! Conditional geometric shell for indexed joint-owner tuples.
The actual source constructor supplies CRT realization and fine-orbital
reconstruction separately. Finite owner images remain literal set images. -/

universe uCompare
namespace CCO.Owners.Joint
open CCO.Owners.Product

variable {G I A Ω : Type*} {Q O : I → Type*}
variable [Group G] [MulAction G A] [MulAction G Ω]
variable [∀ i, MulAction G (Q i)] [∀ i, MulAction G (O i)]

structure AmbientGeometry where
  diagram : OwnerDiagram.{_, _, _, uCompare} I Ω O
  own : ∀ i, Q i → O i
  coordinate : ∀ i, A → Q i
  joint : A → Ω
  equiv_own : ∀ i (g : G) x, own i (g • x) = g • own i x
  equiv_coordinate : ∀ i (g : G) x, coordinate i (g • x) = g • coordinate i x
  equiv_joint : ∀ (g : G) x, joint (g • x) = g • joint x
  equiv_beta : ∀ i (g : G) x, diagram.beta i (g • x) = g • diagram.beta i x
  joint_commute : ∀ i x, own i (coordinate i x) = diagram.beta i (joint x)
  full : A ≃ Carrier diagram Q own
  full_apply : ∀ x i, (full x).val i = coordinate i x
  fine : ∀ a b x y,
    (∀ i, GroupActions.orbital (G := G) (coordinate i a) (coordinate i b)
      (coordinate i x) (coordinate i y)) ↔ GroupActions.orbital (G := G) a b x y

namespace AmbientGeometry
variable (P : AmbientGeometry (G := G) (I := I) (A := A) (Ω := Ω) (Q := Q) (O := O))

/-- The coordinate owner sets are the ACTUAL images of the displayed B. -/
def OwnerImage (B : Set Ω) (i : I) : Set (O i) := P.diagram.beta i '' B

instance ownerImage_finite (B : Set Ω) [Finite B] (i : I) : Finite (P.OwnerImage B i) := by
  classical
  exact Finite.of_surjective
    (fun b : B => (⟨P.diagram.beta i b.val, ⟨b.val, b.property, rfl⟩⟩ : P.OwnerImage B i))
    (by rintro ⟨x, b, hb, rfl⟩; exact ⟨⟨b, hb⟩, rfl⟩)

/-- Restriction retains all the literal comparison tests; its beta maps
are onto by image formation, and jointly separating by the ambient diagram. -/
def finiteDiagram (B : Set Ω) : OwnerDiagram I B (fun i => P.OwnerImage B i) where
  beta i b := ⟨P.diagram.beta i b.val, ⟨b.val, b.property, rfl⟩⟩
  beta_surjective i := by
    rintro ⟨x, b, hb, rfl⟩
    exact ⟨⟨b, hb⟩, rfl⟩
  jointly_injective b c h := by
    apply Subtype.ext
    exact P.diagram.jointly_injective b.val c.val (fun i => congrArg Subtype.val (h i))
  Comparison := P.diagram.Comparison
  left i j b := P.diagram.left i j b.val
  right i j b := P.diagram.right i j b.val
  commute b i j := P.diagram.commute b.val i j

variable (B : Set Ω) (D : ∀ i, Set (Q i))
variable (hD : ∀ i (d : D i), P.own i d.val ∈ P.OwnerImage B i)

/-- Every factor map lands in its complete projected finite owner image. -/
def finiteOwn (i : I) (d : D i) : P.OwnerImage B i := ⟨P.own i d.val, hD i d⟩

abbrev Witness := Carrier (P.finiteDiagram B) (fun i => D i) (P.finiteOwn B D hD)

/-- The CRT realization of the WHOLE finite tuple, with no owner-fullness
assumption needed for this carrier injection. -/
noncomputable def point (w : P.Witness B D hD) : A :=
  P.full.symm ⟨fun i => (w.val i).val, w.property⟩

@[simp] theorem point_coordinate (w : P.Witness B D hD) (i : I) :
    P.coordinate i (P.point B D hD w) = (w.val i).val := by
  simpa only [point, Equiv.apply_symm_apply] using
    (P.full_apply (P.point B D hD w) i).symm

theorem point_injective : Function.Injective (P.point B D hD) := by
  intro w z hwz
  apply Subtype.ext
  funext i
  apply Subtype.ext
  exact (P.point_coordinate B D hD w i).symm.trans
    ((congrArg (P.coordinate i) hwz).trans (P.point_coordinate B D hD z i))

/-- The finite full-owner identification is the literal ambient joint
projection, rather than an independently chosen tuple label. -/
theorem joint_point (fullB : FullOwners (P.finiteDiagram B))
    (w : P.Witness B D hD) :
    P.joint (P.point B D hD w) = (owner (P.finiteDiagram B) (fun i => D i)
      (P.finiteOwn B D hD) fullB w).val := by
  apply P.diagram.jointly_injective
  intro i
  calc
    P.diagram.beta i (P.joint (P.point B D hD w)) =
        P.own i (P.coordinate i (P.point B D hD w)) := (P.joint_commute i _).symm
    _ = P.own i (w.val i).val := congrArg (P.own i) (P.point_coordinate B D hD w i)
    _ = _ := (congrArg Subtype.val
      (beta_owner (P.finiteDiagram B) (fun i => D i) (P.finiteOwn B D hD) fullB w i)).symm

variable (surjD : ∀ i, Function.Surjective (P.finiteOwn B D hD i))

/-- Full and sparse coordinate descent, using its onto map WITHOUT
finite-owner fullness. The old-orbital kernel and all target colours are
recognized by the equivariant ambient coordinate map. -/
def coordinateQuotient (i : I) :
    OrbitalQuotient (G := G) (P.point B D hD) (Subtype.val : D i → Q i) where
  ambient := P.coordinate i
  equivariant := P.equiv_coordinate i
  projection w := w.val i
  surjective := coordinate_surjective (P.finiteDiagram B) (fun i => D i)
    (P.finiteOwn B D hD) surjD i
  target_injective := Subtype.val_injective
  commutes w := (P.point_coordinate B D hD w i).symm

/-- Full and sparse descent to the COMPLETE joint-owner set. -/
noncomputable def ownerQuotient (fullB : FullOwners (P.finiteDiagram B)) :
    OrbitalQuotient (G := G) (P.point B D hD) (Subtype.val : B → Ω) where
  ambient := P.joint
  equivariant := P.equiv_joint
  projection := owner (P.finiteDiagram B) (fun i => D i) (P.finiteOwn B D hD) fullB
  surjective := owner_surjective (P.finiteDiagram B) (fun i => D i)
    (P.finiteOwn B D hD) fullB surjD
  target_injective := Subtype.val_injective
  commutes w := (P.joint_point B D hD fullB w).symm

/-- Factor automorphisms descend on ALL factor owners. -/
def factorOwnerQuotient (i : I) :
    OrbitalQuotient (G := G) (Subtype.val : D i → Q i)
      (Subtype.val : P.OwnerImage B i → O i) where
  ambient := P.own i
  equivariant := P.equiv_own i
  projection := P.finiteOwn B D hD i
  surjective := surjD i
  target_injective := Subtype.val_injective
  commutes _ := rfl

/-- Every full joint-owner automorphism has a canonical coordinate action;
individual action-surjectivity is not asserted or needed. -/
def jointOwnerQuotient (i : I) :
    OrbitalQuotient (G := G) (Subtype.val : B → Ω)
      (Subtype.val : P.OwnerImage B i → O i) where
  ambient := P.diagram.beta i
  equivariant := P.equiv_beta i
  projection := (P.finiteDiagram B).beta i
  surjective := (P.finiteDiagram B).beta_surjective i
  target_injective := Subtype.val_injective
  commutes _ := rfl

/-- The literal induced original carrier above all factor sets. -/
def inducedCarrier : Set A := {x | ∀ i, P.coordinate i x ∈ D i}

noncomputable def pointCarrierEquiv : P.Witness B D hD ≃ P.inducedCarrier D where
  toFun w := ⟨P.point B D hD w, by
    intro i
    rw [P.point_coordinate]
    exact (w.val i).property⟩
  invFun x := ⟨fun i => ⟨P.coordinate i x.val, x.property i⟩, by
    change CompatibleOwner P.diagram (fun i => P.own i (P.coordinate i x.val))
    have h := (P.full x.val).property
    simpa only [P.full_apply] using h⟩
  left_inv w := by
    apply Subtype.ext
    funext i
    apply Subtype.ext
    exact P.point_coordinate B D hD w i
  right_inv x := by
    apply Subtype.ext
    apply P.full.injective
    apply Subtype.ext
    funext i
    rw [P.full_apply, P.full_apply]
    exact P.point_coordinate B D hD _ i

/-- Finiteness applies to the actual original subset, never a merely
formal tuple space with an assumed realization map. -/
theorem inducedCarrier_finite [Finite I] [∀ i, Finite (D i)] : Finite (P.inducedCarrier D) := by
  apply Finite.of_injective
    (fun x : P.inducedCarrier D => fun i => (⟨P.coordinate i x.val, x.property i⟩ : D i))
  intro x y h
  apply Subtype.ext
  apply P.full.injective
  apply Subtype.ext
  funext i
  rw [P.full_apply, P.full_apply]
  exact congrArg Subtype.val (congrFun h i)

end AmbientGeometry
end CCO.Owners.Joint
