import CCO.Owners.Joint.Carrier
import CCO.Owners.Joint.GenericDescent
import CCO.Owners.Joint.Matching

/-! The genuinely generic finite binary-language branch. It assumes only
the named-kernel/colour recognition and fine readout in A05–A06, and does
not assume a common ambient orbital action or any group-lifting provider. -/
universe uUnary uBinary
namespace CCO.Owners.Joint.Relational
open CCO.FiniteKernel
variable {I B : Type*} {Bi Di : I → Type*}
variable (d : OwnerDiagram I B Bi) (full : FullOwners d) (π : ∀ i, Di i → Bi i)

structure LanguageDiagram where
  ownerStructure : BinaryStructure.{_,uUnary,uBinary} B
  ownerCoordinateStructure : ∀ i, BinaryStructure.{_,uUnary,uBinary} (Bi i)
  factorStructure : ∀ i, BinaryStructure.{_,uUnary,uBinary} (Di i)
  witnessStructure : BinaryStructure.{_,uUnary,uBinary} (Carrier d Di π)
  factorOwner : ∀ i, RecognizableQuotient (factorStructure i) (ownerCoordinateStructure i)
  factorOwner_projection : ∀ i x, (factorOwner i).projection x = π i x
  jointOwner : ∀ i, RecognizableQuotient ownerStructure (ownerCoordinateStructure i)
  jointOwner_projection : ∀ i b, (jointOwner i).projection b = d.beta i b
  toFactor : ∀ i, RecognizableQuotient witnessStructure (factorStructure i)
  toFactor_projection : ∀ i w, (toFactor i).projection w = w.val i
  toOwner : RecognizableQuotient witnessStructure ownerStructure
  toOwner_projection : ∀ w, toOwner.projection w = owner d Di π full w
  fine : ∀ a b x y : Carrier d Di π,
    (∀ i, SamePair (factorStructure i) (a.val i) (b.val i) (x.val i) (y.val i)) →
      SamePair witnessStructure a b x y

namespace LanguageDiagram
variable {d full π}
variable (L : LanguageDiagram d full π)

noncomputable def factorAction (i : I) := (L.factorOwner i).action
noncomputable def jointAction (i : I) := (L.jointOwner i).action

theorem factor_action (i : I) (g : (L.factorStructure i).Aut) (x : Di i) :
    (L.factorAction i g).val (π i x) = π i (g.val x) := by
  simpa only [factorAction, L.factorOwner_projection] using (L.factorOwner i).action_projection g x

theorem joint_action (i : I) (g : L.ownerStructure.Aut) (b : B) :
    (L.jointAction i g).val (d.beta i b) = d.beta i (g.val b) := by
  simpa only [jointAction, L.jointOwner_projection] using (L.jointOwner i).action_projection g b

theorem coordinate_action (i : I) (g : L.witnessStructure.Aut) (w : Carrier d Di π) :
    (((L.toFactor i).action g).val (w.val i)) = (g.val w).val i := by
  simpa only [L.toFactor_projection] using (L.toFactor i).action_projection g w

theorem owner_action (g : L.witnessStructure.Aut) (w : Carrier d Di π) :
    (L.toOwner.action g).val (owner d Di π full w) = owner d Di π full (g.val w) := by
  simpa only [L.toOwner_projection] using L.toOwner.action_projection g w

theorem owner_coordinate (w : Carrier d Di π) (i : I) :
    π i ((L.toFactor i).projection w) = d.beta i (L.toOwner.projection w) := by
  rw [L.toFactor_projection, L.toOwner_projection]
  exact (beta_owner d Di π full w i).symm

end LanguageDiagram
end CCO.Owners.Joint.Relational

