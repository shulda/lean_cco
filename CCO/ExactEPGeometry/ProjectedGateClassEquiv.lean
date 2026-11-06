import CCO.RigidGroupoid.Geometry.ProjectedKernels

/-!
# B062 C86/C93: a finer quotient below a full gate cannot collapse gate classes

Let E be a surjective quotient kernel and K a genuine old exact gate
with E ≤ K. The resulting projected gate K/E has exactly the same
set of gate classes as K. This is a genuine quotient equivalence,
proved from the full pullback of K/E and the surjectivity of the
actual quotient map. The projected gate is NOT logical identity.

The intended consumer instantiates this lemma with the real current
E|p² kernel, the selected quotient class transport and the actual
full-RAW-exact C82 projected gates. No section of automorphism
groups, SAP or converse arbitrary mixed RAW descent is assumed.
-/

universe u v w q

namespace CCO.ExactEPGeometry

open RigidGroupoid.Geometry

noncomputable section

variable {ι : Type u} {X : ι → Type v} {Q : ι → Type q}
variable {S : AtomicSource.{u,v,w} ι X}
variable {i : ι} (K : Kernel S i) (pi : X i → Q i)
variable (surj : Function.Surjective pi)
variable (nested : ∀ x y, pi x = pi y → K.rel x y)

/-- The literal class map from the true K-quotient of old points to the
genuinely projected K/E-quotient class on the finer E-carrier. -/
noncomputable def projectedGateClassMap :
    K.Class → Quotient (K.projectedSetoid pi surj nested) :=
  Quotient.lift
    (fun x => (Quotient.mk'' (pi x) :
      Quotient (K.projectedSetoid pi surj nested)))
    (fun x y h => Quotient.sound ⟨x,y,rfl,rfl,h⟩)

/-- No TWO distinct original full K-gate classes become one class after
quotienting by an actual E≤K. This uses the whole projected pullback,
not the logical E-kernel in place of K. -/
theorem projectedGateClassMap_injective :
    Function.Injective (projectedGateClassMap K pi surj nested) := by
  intro a b hab
  induction a using Quotient.inductionOn with
  | _ x =>
    induction b using Quotient.inductionOn with
    | _ y =>
      apply Quotient.sound
      have h : (K.projectedSetoid pi surj nested).r (pi x) (pi y) :=
        Quotient.exact hab
      have hp := congrFun (congrFun
        (K.projected_pullback pi surj nested) x) y
      exact (Iff.of_eq hp).mp h

/-- Every actual projected K/E-class has a genuine old K-class
preimage, since the actual E projection is surjective. -/
theorem projectedGateClassMap_surjective :
    Function.Surjective (projectedGateClassMap K pi surj nested) := by
  intro q
  induction q using Quotient.inductionOn with
  | _ y =>
    obtain ⟨x,rfl⟩ := surj y
    exact ⟨Quotient.mk'' x,rfl⟩

/-- The actual canonical equivalence between old K classes and the
complete projected K/E gate classes. No arbitrary choice of a
point representative is needed in the forward map. -/
noncomputable def projectedGateClassEquiv :
    K.Class ≃ Quotient (K.projectedSetoid pi surj nested) :=
  Equiv.ofBijective
    (projectedGateClassMap K pi surj nested)
    ⟨projectedGateClassMap_injective K pi surj nested,
      projectedGateClassMap_surjective K pi surj nested⟩

/-- The equivalence maps any genuine old representative to the
projected gate class of its ACTUAL E-class. -/
theorem projectedGateClassEquiv_mk (x : X i) :
    projectedGateClassEquiv K pi surj nested (K.project x) =
      Quotient.mk'' (pi x) := rfl

end
end CCO.ExactEPGeometry
