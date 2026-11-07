import CCO.UnfilteredEP.OrderedAmalgamNormalized
import CCO.UnfilteredEP.HierarchyFixedMaps

/-! Actual strong amalgamation in the SAME full normalized class used
by Ramsey and the relative reset tasks. Coding and model casts retain
the original point maps and the exact intersection clause. -/

set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace CCO.UnfilteredEP
open APRamseyReadout CloneTupleGeometry FullCode
noncomputable section
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal)

theorem normalizedProperAge_strong
    (priority : LinearOrder (Sig B ht).Sorts)
    (Root Left Right : FiniteHidden.{max u v w,max u v} (OrderedCoordinateLanguage B ht))
    (hH : NormalizedProperAge B ht priority Root)
    (hL : NormalizedProperAge B ht priority Left)
    (hR : NormalizedProperAge B ht priority Right)
    (sL : Structure.Embedding Root.model Left.model)
    (sR : Structure.Embedding Root.model Right.model) :
    ∃ C : FiniteHidden.{max u v w,max u v} (OrderedCoordinateLanguage B ht),
      NormalizedProperAge B ht priority C ∧
      ∃ (f : Structure.Embedding Left.model C.model)
        (g : Structure.Embedding Right.model C.model),
        (∀ p, f.point (sL.point p) = g.point (sR.point p)) ∧
        (∀ a b, f.point a = g.point b → ∃ p, a = sL.point p ∧ b = sR.point p) := by
  let P := normalizedPresentation B ht priority hH
  let Q := normalizedPresentation B ht priority hL
  let R := normalizedPresentation B ht priority hR
  letI := P.order
  letI := Q.order
  letI := R.order
  let l := TerminalHiddenHN.orderedEmbeddingInverse (Sig B ht)
    (TerminalHiddenHN.sig_binary (cloneSource B) (cloneHomogeneous B) (cloneSAP B) (fullCovers B ht))
    (FullEmbedding.castModels sL P.model_eq Q.model_eq)
  let r := TerminalHiddenHN.orderedEmbeddingInverse (Sig B ht)
    (TerminalHiddenHN.sig_binary (cloneSource B) (cloneHomogeneous B) (cloneSAP B) (fullCovers B ht))
    (FullEmbedding.castModels sR P.model_eq R.model_eq)
  have ml : StrictMono l.point := fun _ _ h => (l.order_iff _ _).mpr h
  have mr : StrictMono r.point := fun _ _ h => (r.order_iff _ _).mpr h
  obtain ⟨Z,finite,C,hC,o,f,g,fixed,commute,strong,orderedL,orderedR⟩ :=
    proper_hidden_normalized_strong B ht priority P.raw Q.raw R.raw
      ⟨Q.actual,Q.proper⟩ ⟨R.actual,R.proper⟩ Q.fixed R.fixed l.toEmbedding r.toEmbedding ml mr
  letI := finite
  letI := o
  let target : FiniteHidden (OrderedCoordinateLanguage B ht) :=
    ⟨Z,@OrderedCoordinateModel B ht Z C o,finite⟩
  let f0 := TerminalHiddenHN.orderedEmbedding (Sig B ht)
    (TerminalHiddenHN.sig_binary (cloneSource B) (cloneHomogeneous B) (cloneSAP B) (fullCovers B ht))
    (show UnaryHN.Raw.OrderedEmbedding Q.raw C from ⟨f,orderedL⟩)
  let g0 := TerminalHiddenHN.orderedEmbedding (Sig B ht)
    (TerminalHiddenHN.sig_binary (cloneSource B) (cloneHomogeneous B) (cloneSAP B) (fullCovers B ht))
    (show UnaryHN.Raw.OrderedEmbedding R.raw C from ⟨g,orderedR⟩)
  let ff : Structure.Embedding Left.model target.model :=
    FullEmbedding.castModels f0 Q.model_eq.symm rfl
  let gg : Structure.Embedding Right.model target.model :=
    FullEmbedding.castModels g0 R.model_eq.symm rfl
  have ffpoint (x) : ff.point x = f.point x := FullEmbedding.castModels_point _ _ _ _
  have ggpoint (x) : gg.point x = g.point x := FullEmbedding.castModels_point _ _ _ _
  have lpoint (x) : l.point x = sL.point x := FullEmbedding.castModels_point _ _ _ _
  have rpoint (x) : r.point x = sR.point x := FullEmbedding.castModels_point _ _ _ _
  refine ⟨target,⟨C,o,hC.1,hC.2,fixed,rfl⟩,ff,gg,?_,?_⟩
  · intro p
    rw [ffpoint,ggpoint,← lpoint,← rpoint]
    exact commute p
  · intro a b equal
    rw [ffpoint,ggpoint] at equal
    obtain ⟨p,hp,hp'⟩ := strong a b equal
    exact ⟨p,hp.trans (lpoint p),hp'.trans (rpoint p)⟩

end
end CCO.UnfilteredEP
