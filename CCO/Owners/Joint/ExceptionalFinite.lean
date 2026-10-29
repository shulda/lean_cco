import CCO.Owners.Joint.Exceptional
import CCO.Owners.Joint.FullAutomorphisms

/-! The retained exceptional action is assembled into the ENTIRE full
finite structural group. The original input root and all target packets
remain visible; no root/rank provider is discharged by this conditional lemma. -/
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

include fullB

/-- C23–26 in the actual finite structural groups. The prescribed
exceptional automorphism is retained on its ENTIRE factor. -/
theorem exceptional_finite
    (factorLift : ∀ i, GroupActions.PrescribedLift
      (P.factorAction B D hD surjD i) (P.finiteOwn B D hD i))
    (e : I) (A0 Z : Set (P.Witness B D hD)) (z : P.Witness B D hD) (hz : z ∈ Z)
    (target : ∀ i, Set (D i)) (F : ∀ i, Setoid (D i))
    (invariantF : ∀ i (k : OrbitalAut G (Q i) (Subtype.val : D i → Q i)) x y,
      F i x y → F i (k.val x) (k.val y))
    (closedTarget : ∀ i (a : P.Witness B D hD), a ∈ A0 →
      ∀ y, F i (a.val i) y → y ∈ target i)
    (clique : ∀ i, i ≠ e → ∀ w ∈ Z, F i (z.val i) (w.val i))
    (exceptional : OrbitalAut G (Q e) (Subtype.val : D e → Q e))
    (exceptionalZ : ∀ w ∈ Z, exceptional.val (w.val e) ∈ target e)
    (exceptionalRoot : exceptional.val (z.val e) ∈
      (fun w : P.Witness B D hD => w.val e) '' A0)
    (ownerM3 : Function.Surjective (P.jointAction B e) ∧
      GroupActions.FibreTransitive (P.jointAction B e) ((P.finiteDiagram B).beta e)) :
    ∃ alpha : OrbitalAut G A (P.point B D hD),
      (P.coordinateQuotient B D hD surjD e).action alpha = exceptional ∧
      alpha.val z ∈ A0 ∧ ∀ w ∈ Z, ∀ i, (alpha.val w).val i ∈ target i := by
  let eqπ := fun i g x =>
    ((P.factorOwnerQuotient B D hD surjD i).action_projection g x).symm
  let eqβ := fun i g x => ((P.jointOwnerQuotient B i).action_projection g x).symm
  letI := witnessAction (P.finiteDiagram B) fullB (P.finiteOwn B D hD)
    (P.factorAction B D hD surjD) (P.jointAction B) eqπ eqβ
  obtain ⟨k,hke,hroot,htarget⟩ := exceptional_target
    (P.finiteDiagram B) fullB (P.finiteOwn B D hD)
    (P.factorAction B D hD surjD) (P.jointAction B) eqπ eqβ factorLift
    e A0 Z z hz target F invariantF closedTarget clique exceptional exceptionalZ exceptionalRoot ownerM3
  refine ⟨P.lift B D hD surjD fullB k,?_,hroot,htarget⟩
  apply Subtype.ext
  apply Equiv.ext
  intro x
  obtain ⟨w,rfl⟩ := (P.coordinateQuotient B D hD surjD e).surjective x
  rw [OrbitalQuotient.action_projection]
  change ((P.lift B D hD surjD fullB k).val w).val e = exceptional.val (w.val e)
  rw [P.lift_coordinate, hke]

end AmbientGeometry
end CCO.Owners.Joint

