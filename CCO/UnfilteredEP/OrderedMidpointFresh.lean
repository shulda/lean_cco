import CCO.UnfilteredEP.OrderedAmalgamNormalized

/-! The ordered strong intersection conclusion is used over the WHOLE
closed base. An off-base point of the right factor is therefore fresh
over every point of the prescribed left factor, while both complete
orders and their actual fine diagrams are retained. -/

universe u v w
namespace CCO.UnfilteredEP
open APRamseyReadout CloneTupleGeometry UnarySupport
noncomputable section
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal)

theorem proper_hidden_normalized_fresh_amalgam
    (priority : LinearOrder (Sig B ht).Sorts)
    {H V W : Type (max u v)}
    (Root : Structure (Sig B ht) H)
    (Left : Structure (Sig B ht) V) (Right : Structure (Sig B ht) W)
    [oH : LinearOrder H] [oV : LinearOrder V] [oW : LinearOrder W]
    (hL : ProperAge B ht Left) (hR : ProperAge B ht Right)
    (fixedL : hierarchicalOrder B ht Left hL.2 hL.1 priority oV = oV)
    (fixedR : hierarchicalOrder B ht Right hR.2 hR.1 priority oW = oW)
    (sL : Root.Embedding Left) (sR : Root.Embedding Right)
    (leftOrdered : StrictMono sL.point) (rightOrdered : StrictMono sR.point)
    (z : W) (fresh : z ∉ Set.range sR.point) :
    ∃ (Z : Type (max u v)) (_ : Finite Z)
      (C : Structure (Sig B ht) Z) (hC : ProperAge B ht C),
      ∃ (o : LinearOrder Z) (f : Left.Embedding C) (g : Right.Embedding C),
        hierarchicalOrder B ht C hC.2 hC.1 priority o = o ∧
        (∀ p, f.point (sL.point p) = g.point (sR.point p)) ∧
        g.point z ∉ Set.range f.point ∧
        (∀ x y, @LT.lt Z o.toLT (f.point x) (f.point y) ↔ x < y) ∧
        (∀ x y, @LT.lt Z o.toLT (g.point x) (g.point y) ↔ x < y) := by
  obtain ⟨Z,finite,C,hC,o,f,g,fixed,commute,strong,orderedL,orderedR⟩ :=
    proper_hidden_normalized_strong B ht priority Root Left Right hL hR
      fixedL fixedR sL sR leftOrdered rightOrdered
  refine ⟨Z,finite,C,hC,o,f,g,fixed,commute,?_,orderedL,orderedR⟩
  rintro ⟨a,ha⟩
  obtain ⟨p,_,hp⟩ := strong a z ha
  exact fresh ⟨p,hp.symm⟩

end
end CCO.UnfilteredEP
