import CCO.UnfilteredEP.OrderedAmalgamActual
import CCO.UnfilteredEP.HierarchyMaps

/-! Actual synchronized normalized SAP is PROVED by constructing the
whole-order proper amalgam and applying the actual same-map hierarchical
normalizer. Each normalized factor is fixed by idempotence; all original
point maps, fine cylinders and exact strong intersection are retained. -/

universe u v w
namespace CCO.UnfilteredEP
open APRamseyReadout CloneTupleGeometry UnarySupport
noncomputable section
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal)

/-- The actual synchronized normalized class has strong amalgamation.
This result uses its concrete FULL keys/inverse-path normalizer, not an
assumed ordered-SAP gate or the generic Ramsey normalization theorem. -/
theorem proper_hidden_normalized_strong
    (priority : LinearOrder (Sig B ht).Sorts)
    {H V W : Type (max u v)}
    (Root : Structure (Sig B ht) H)
    (Left : Structure (Sig B ht) V) (Right : Structure (Sig B ht) W)
    [oH : LinearOrder H] [oV : LinearOrder V] [oW : LinearOrder W]
    (hL : ProperAge B ht Left) (hR : ProperAge B ht Right)
    (fixedL : hierarchicalOrder B ht Left hL.2 hL.1 priority oV = oV)
    (fixedR : hierarchicalOrder B ht Right hR.2 hR.1 priority oW = oW)
    (sL : Root.Embedding Left) (sR : Root.Embedding Right)
    (leftOrdered : StrictMono sL.point) (rightOrdered : StrictMono sR.point) :
    ∃ (Z : Type (max u v)) (_ : Finite Z)
      (C : Structure (Sig B ht) Z) (hC : ProperAge B ht C),
      ∃ (o : LinearOrder Z) (f : Left.Embedding C) (g : Right.Embedding C),
        hierarchicalOrder B ht C hC.2 hC.1 priority o = o ∧
        (∀ p, f.point (sL.point p) = g.point (sR.point p)) ∧
        (∀ a b, f.point a = g.point b → ∃ p, a = sL.point p ∧ b = sR.point p) ∧
        (∀ x y, @LT.lt Z o.toLT (f.point x) (f.point y) ↔ x < y) ∧
        (∀ x y, @LT.lt Z o.toLT (g.point x) (g.point y) ↔ x < y) := by
  obtain ⟨Z,finite,C,hC,o,f,g,commute,strong,orderedL,orderedR⟩ :=
    proper_hidden_all_orders_strong B ht Root Left Right hL hR sL sR leftOrdered rightOrdered
  let normalized := hierarchicalOrder B ht C hC.2 hC.1 priority o
  refine ⟨Z,finite,C,hC,normalized,f,g,?_,commute,strong,?_,?_⟩
  · exact hierarchicalOrder_idempotent B ht C hC.2 hC.1 priority o
  · intro x y
    have law := hierarchicalOrder_map_iff B ht hL.1 hC.1 f oV o orderedL hL.2 hC.2 priority x y
    rw [fixedL] at law
    exact law
  · intro x y
    have law := hierarchicalOrder_map_iff B ht hR.1 hC.1 g oW o orderedR hR.2 hC.2 priority x y
    rw [fixedR] at law
    exact law

end
end CCO.UnfilteredEP
