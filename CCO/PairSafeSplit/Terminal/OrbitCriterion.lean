import CCO.OwnerTransversal.TypedOrbitSAP
import CCO.StabilizerHomogeneity
import Mathlib.Data.Fintype.Card
import Lean.Elab.Tactic.Omega

/-! B047 C30--C32, generic relational closure(A)=A support. Arbitrarily
many actual finite-base type witnesses give infinite whole stabilizer
orbits. One simultaneous avoidance automorphism then proves real age SAP.
The actual marked source supplies these witnesses separately. -/

universe u v w t
namespace CCO.PairSafeSplit.SAP
variable {ι : Type u} {X : ι → Type v} (T : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [MulAction G (Sigma X)]

/-- This is a finite multiplicity criterion, not a new SAP assumption.
It is valid in the whole original relational source with no functions,
CCO, countability or pre-existing orbit-infinitude premise. -/
theorem ageSAP_of_many_same_type (H : HomogeneousSource T G)
    (many : ∀ (B : FiniteInduced (X := X)) (x : Sigma X), x ∉ B.vertices →
      ∀ n : ℕ, ∃ f : Fin n ↪ Sigma X,
        ∀ j, RealAction.SameTypeOver T B x (f j)) : AgeSAP T := by
  classical
  apply OwnerTransversal.ageSAP_of_infinite_stabilizer_orbits T H
  intro B x hx hfinite
  letI := hfinite.fintype
  obtain ⟨f,hf⟩ := many B x hx
    (Fintype.card (RealAction.orbitOver (G := G) B.vertices x) + 1)
  let g : Fin (Fintype.card (RealAction.orbitOver (G := G) B.vertices x) + 1) ↪
      (RealAction.orbitOver (G := G) B.vertices x) := {
    toFun j := ⟨f j, RealAction.sameTypeOver_orbit T H B x (f j) (hf j)⟩
    inj' := fun a b h => f.injective (congrArg Subtype.val h) }
  have bound := Fintype.card_le_of_injective g g.injective
  rw [Fintype.card_fin] at bound
  omega

end CCO.PairSafeSplit.SAP
