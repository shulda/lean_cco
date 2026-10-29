import CCO.Owners.Joint.Exceptional
import CCO.Owners.Joint.GenericFullAutomorphisms

/-! The exceptional-map support in arbitrary finite named languages.
Its output keeps the GIVEN entire factor automorphism and one ORIGINAL
input root, with only the compatible finite target conclusion. -/
namespace CCO.Owners.Joint.Relational.LanguageDiagram
variable {I B : Type*} {Bi Di : I → Type*}
variable {d : OwnerDiagram I B Bi} {full : FullOwners d} {π : ∀ i, Di i → Bi i}
variable (L : LanguageDiagram d full π)

theorem exceptional_finite
    (factorLift : ∀ i, GroupActions.PrescribedLift (L.factorAction i) (π i))
    (e : I) (A0 Z : Set (Carrier d Di π)) (z : Carrier d Di π) (hz : z ∈ Z)
    (target : ∀ i, Set (Di i)) (F : ∀ i, Setoid (Di i))
    (invariantF : ∀ i (k : (L.factorStructure i).Aut) x y,
      F i x y → F i (k.val x) (k.val y))
    (closedTarget : ∀ i (a : Carrier d Di π), a ∈ A0 →
      ∀ y, F i (a.val i) y → y ∈ target i)
    (clique : ∀ i, i ≠ e → ∀ w ∈ Z, F i (z.val i) (w.val i))
    (exceptional : (L.factorStructure e).Aut)
    (exceptionalZ : ∀ w ∈ Z, exceptional.val (w.val e) ∈ target e)
    (exceptionalRoot : exceptional.val (z.val e) ∈
      (fun w : Carrier d Di π => w.val e) '' A0)
    (ownerM3 : Function.Surjective (L.jointAction e) ∧
      GroupActions.FibreTransitive (L.jointAction e) (d.beta e)) :
    ∃ alpha : L.witnessStructure.Aut,
      (L.toFactor e).action alpha = exceptional ∧
      alpha.val z ∈ A0 ∧ ∀ w ∈ Z, ∀ i, (alpha.val w).val i ∈ target i := by
  let eqπ := fun i g x => (L.factor_action i g x).symm
  let eqβ := fun i g x => (L.joint_action i g x).symm
  letI := witnessAction d full π L.factorAction L.jointAction eqπ eqβ
  obtain ⟨k,hke,hroot,htarget⟩ := exceptional_target d full π L.factorAction L.jointAction
    eqπ eqβ factorLift e A0 Z z hz target F invariantF closedTarget clique
      exceptional exceptionalZ exceptionalRoot ownerM3
  refine ⟨L.lift k,?_,hroot,htarget⟩
  apply Subtype.ext
  apply Equiv.ext
  intro x
  obtain ⟨w,hw⟩ := (L.toFactor e).surjective x
  rw [← hw, L.toFactor_projection, L.coordinate_action, L.lift_coordinate, hke]

end CCO.Owners.Joint.Relational.LanguageDiagram

