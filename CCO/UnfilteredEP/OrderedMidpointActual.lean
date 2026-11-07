import CCO.UnfilteredEP.OrderedMidpointSource
import CCO.UnfilteredEP.OrderedMidpointFresh
import CCO.UnfilteredEP.ResetCylinder

/-! C65--C66 on the actual source: every prescribed ordered parent
pair has a normalized reset midpoint fresh over the ENTIRE old member.
The two edges use the one existing complete semantic cylinder. -/

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 900000
universe u v w
namespace CCO.UnfilteredEP
open APRamseyReadout CloneTupleGeometry UnarySupport TerminalLattice
noncomputable section
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal)

theorem resetCoordinateBinary_iff {i : B.Sorts} (J : FullCloneProperMI B.source i)
    (m : ActualResetMenu B J) (q t : Quotient J.val.val) :
    (CoordinateTarget B ht).binary (resetCylinderName B ht J m)
      (coordinateNode B ht J q) (coordinateNode B ht J t) ↔ m.relation q t := by
  change CCO.UnaryTermsReturn.originalCompletedCylinderBinaryPredicate (cloneSource B) (HF B)
    (resetCylinderName B ht J m) (coordinateNode B ht J q) (coordinateNode B ht J t) ↔ _
  exact resetCylinderName_iff B ht J m q t

/-- No old comparison, partial graph or fine cylinder is discarded.
The midpoint is fresh over ALL old vertices. Both reset edges are
instances of the SAME actual source-chosen complete named cylinder. -/
theorem actual_normalized_fresh_midpoint
    (priority : LinearOrder (Sig B ht).Sorts) (r : CutOrbit B ht)
    (m : ActualResetMenu B (fullMIOfNamed B (cutRepresentative B ht r).val.1
      (cutRepresentative B ht r).val.2))
    (q t : Quotient (cutRepresentative B ht r).val.2.val.val)
    (hparent : originalUpperSetoid (cloneSource B) (cutRepresentative B ht r).val.2.val
      (fullMIParent B (fullMIOfNamed B (cutRepresentative B ht r).val.1
        (cutRepresentative B ht r).val.2))
      (fullMIParent_cover B (fullMIOfNamed B (cutRepresentative B ht r).val.1
        (cutRepresentative B ht r).val.2)).le q t)
    {V : Type (max u v)} (C : Structure (Sig B ht) V) (hC : ProperAge B ht C)
    (oC : LinearOrder V)
    (fixedC : hierarchicalOrder B ht C hC.2 hC.1 priority oC = oC)
    (s : (cutPairStructure B ht (cutRepresentative B ht r).val q t).Embedding C)
    (comparison : @LT.lt _ oC.toLT (s.point (cutPairLeft B ht _ q t))
      (s.point (cutPairRight B ht _ q t))) :
    ∃ (W : Type (max u v)) (_ : Finite W)
      (D : Structure (Sig B ht) W) (hD : ProperAge B ht D)
      (oD : LinearOrder W) (f : C.Embedding D),
      hierarchicalOrder B ht D hD.2 hD.1 priority oD = oD ∧
      (∀ x y, @LT.lt _ oD.toLT (f.point x) (f.point y) ↔ @LT.lt _ oC.toLT x y) ∧
      ∃ z : W, z ∉ Set.range f.point ∧
        D.sort z = hiddenCutSort B ht (cutRepresentative B ht r).val ∧
        @LT.lt _ oD.toLT (f.point (s.point (cutPairLeft B ht _ q t))) z ∧
        @LT.lt _ oD.toLT z (f.point (s.point (cutPairRight B ht _ q t))) ∧
        (CoordinateModel B ht D).binary (resetCylinderName B ht _ m)
          (f.point (s.point (cutPairLeft B ht _ q t))) z ∧
        (CoordinateModel B ht D).binary (resetCylinderName B ht _ m)
          z (f.point (s.point (cutPairRight B ht _ q t))) := by
  let cut := (cutRepresentative B ht r).val
  let J := fullMIOfNamed B cut.1 cut.2
  let P := cutPairStructure B ht cut q t
  have hP := cutPair_mem B ht cut q t
  let oP : LinearOrder (cutPairSet B ht cut q t) := LinearOrder.lift' s.point s.injective
  have fixedP : hierarchicalOrder B ht P hP.2 hP.1 priority oP = oP := by
    apply LinearOrder.ext_lt
    intro x y
    have law := hierarchicalOrder_map_iff B ht hP.1 hC.1 s oP oC (fun _ _ => Iff.rfl)
      hP.2 hC.2 priority x y
    rw [fixedC] at law
    exact law.symm
  obtain ⟨z,hqz,hzt,fresh,hT,oT,fixedT,keeps,middle,hm,before,after⟩ :=
    actual_reset_normalized_closed_pair_witness B ht priority r m q t hparent oP fixedP comparison
  let T := cutTripleStructure B ht cut q t z
  let e := cutPairIntoTriple B ht cut q t z
  have freshMiddle : middle ∉ Set.range e.point := by
    rintro ⟨p,hp⟩
    have hv : p.val = namedNode B cut.2 z := (congrArg Subtype.val hp).trans hm
    apply fresh
    rw [← hv]
    exact p.property
  let inc : T.Embedding (Target B ht) := (Target B ht).inclusion
    (cutTripleSet B ht cut q t z) ((Target B ht).isClosed_closure _)
  let ib := TerminalHiddenHN.binaryEmbedding (Sig B ht)
    (TerminalHiddenHN.sig_binary (cloneSource B) (cloneHomogeneous B) (cloneSAP B) (fullCovers B ht)) inc
  have firstEdge : (CoordinateModel B ht T).binary (resetCylinderName B ht J m)
      (e.point (cutPairLeft B ht cut q t)) middle := by
    apply (ib.binary_iff _ _ _).mp
    change (CoordinateTarget B ht).binary (resetCylinderName B ht J m)
      (namedNode B cut.2 q) middle.val
    rw [hm]
    exact (resetCoordinateBinary_iff B ht J m q z).mpr hqz
  have secondEdge : (CoordinateModel B ht T).binary (resetCylinderName B ht J m)
      middle (e.point (cutPairRight B ht cut q t)) := by
    apply (ib.binary_iff _ _ _).mp
    change (CoordinateTarget B ht).binary (resetCylinderName B ht J m)
      middle.val (namedNode B cut.2 t)
    rw [hm]
    exact (resetCoordinateBinary_iff B ht J m z t).mpr hzt
  letI : LinearOrder ((Target B ht).closure {namedNode B cut.2 q,namedNode B cut.2 t}) := oP
  letI := oC
  letI : LinearOrder ((Target B ht).closure
      {namedNode B cut.2 q,namedNode B cut.2 t,namedNode B cut.2 z}) := oT
  have orderedS : StrictMono s.point := fun _ _ h => h
  have orderedE : StrictMono e.point := fun _ _ h => (keeps _ _).mpr h
  obtain ⟨W,finite,D,hD,oD,f,g,fixedD,commute,freshD,orderedC,orderedT⟩ :=
    proper_hidden_normalized_fresh_amalgam B ht priority P C T hC hT fixedC fixedT
      s e orderedS orderedE middle freshMiddle
  let gb := TerminalHiddenHN.binaryEmbedding (Sig B ht)
    (TerminalHiddenHN.sig_binary (cloneSource B) (cloneHomogeneous B) (cloneSAP B) (fullCovers B ht)) g
  refine ⟨W,finite,D,hD,oD,f,fixedD,orderedC,g.point middle,freshD,?_,?_,?_,?_,?_⟩
  · exact (g.sort_eq middle).trans (congrArg (Target B ht).sort hm)
  · rw [commute]
    exact (orderedT _ _).mpr before
  · rw [commute]
    exact (orderedT _ _).mpr after
  · rw [commute]
    exact (gb.binary_iff _ _ _).mpr firstEdge
  · rw [commute]
    exact (gb.binary_iff _ _ _).mpr secondEdge

end
end CCO.UnfilteredEP
