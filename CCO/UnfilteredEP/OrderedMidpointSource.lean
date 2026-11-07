import CCO.UnfilteredEP.OrderedMidpointNormalized
import CCO.UnfilteredEP.ResetPairWitness
import CCO.UnfilteredEP.ProperFreshAmalgam

/-! A genuine complete reset orbital supplies the free normalized
ordered witness on the ENTIRE generated pair and triple closures. The
parent keys required by the insertion theorem are discharged using the
actual quotient parent and every named strict coarser coordinate. -/

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 900000
universe u v w
namespace CCO.UnfilteredEP
open APRamseyReadout CloneTupleGeometry UnarySupport TerminalLattice
noncomputable section
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal)

def cutPairSet (D : HiddenCut B) (q t : Quotient D.2.val.val) : Set (Values B) :=
  (Target B ht).closure {namedNode B D.2 q,namedNode B D.2 t}

def cutTripleSet (D : HiddenCut B) (q t z : Quotient D.2.val.val) : Set (Values B) :=
  (Target B ht).closure {namedNode B D.2 q,namedNode B D.2 t,namedNode B D.2 z}

def cutPairLeft (D : HiddenCut B) (q t : Quotient D.2.val.val) : cutPairSet B ht D q t :=
  ⟨namedNode B D.2 q,(Target B ht).subset_closure _ (by simp)⟩

def cutPairRight (D : HiddenCut B) (q t : Quotient D.2.val.val) : cutPairSet B ht D q t :=
  ⟨namedNode B D.2 t,(Target B ht).subset_closure _ (by simp)⟩

abbrev cutPairStructure (D : HiddenCut B) (q t : Quotient D.2.val.val) :=
  (Target B ht).closureStructure {namedNode B D.2 q,namedNode B D.2 t}

abbrev cutTripleStructure (D : HiddenCut B) (q t z : Quotient D.2.val.val) :=
  (Target B ht).closureStructure {namedNode B D.2 q,namedNode B D.2 t,namedNode B D.2 z}

theorem cutPair_mem (D : HiddenCut B) (q t : Quotient D.2.val.val) :
    ProperAge B ht (cutPairStructure B ht D q t) := by
  apply proper_target_closure_member
  · exact (Set.finite_singleton _).insert _
  · intro x hx
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;> trivial

def cutPairIntoTriple (D : HiddenCut B) (q t z : Quotient D.2.val.val) :
    (cutPairStructure B ht D q t).Embedding (cutTripleStructure B ht D q t z) :=
  properClosedInclusion B ht ((Target B ht).isClosed_closure _)
    ((Target B ht).isClosed_closure _)
    ((Target B ht).closure_mono (by intro a ha; simpa only [Set.mem_insert_iff,
      Set.mem_singleton_iff] using Or.imp_right (fun h => Or.inl h) ha))

/-- C65: the actual source reset creates a point outside the WHOLE old
pair closure, and its entire triple closure has a legal normalized
order extending EVERY old comparison with q < z < t. -/
theorem actual_reset_normalized_closed_pair_witness
    (priority : LinearOrder (Sig B ht).Sorts) (r : CutOrbit B ht)
    (m : ActualResetMenu B (fullMIOfNamed B (cutRepresentative B ht r).val.1
      (cutRepresentative B ht r).val.2))
    (q t : Quotient (cutRepresentative B ht r).val.2.val.val)
    (hparent : originalUpperSetoid (cloneSource B) (cutRepresentative B ht r).val.2.val
      (fullMIParent B (fullMIOfNamed B (cutRepresentative B ht r).val.1
        (cutRepresentative B ht r).val.2))
      (fullMIParent_cover B (fullMIOfNamed B (cutRepresentative B ht r).val.1
        (cutRepresentative B ht r).val.2)).le q t)
    (oP : LinearOrder (cutPairSet B ht (cutRepresentative B ht r).val q t))
    (fixed : hierarchicalOrder B ht _ (cutPair_mem B ht _ q t).2
      (cutPair_mem B ht _ q t).1 priority oP = oP)
    (comparison : @LT.lt _ oP.toLT (cutPairLeft B ht _ q t) (cutPairRight B ht _ q t)) :
    ∃ z : Quotient (cutRepresentative B ht r).val.2.val.val,
      m.relation q z ∧ m.relation z t ∧
      namedNode B (cutRepresentative B ht r).val.2 z ∉
        cutPairSet B ht (cutRepresentative B ht r).val q t ∧
      ∃ (hT : ProperAge B ht (cutTripleStructure B ht (cutRepresentative B ht r).val q t z))
        (oT : LinearOrder (cutTripleSet B ht (cutRepresentative B ht r).val q t z)),
        hierarchicalOrder B ht _ hT.2 hT.1 priority oT = oT ∧
        (∀ x y, @LT.lt _ oT.toLT ((cutPairIntoTriple B ht _ q t z).point x)
          ((cutPairIntoTriple B ht _ q t z).point y) ↔ @LT.lt _ oP.toLT x y) ∧
        ∃ middle : cutTripleSet B ht (cutRepresentative B ht r).val q t z,
          middle.val = namedNode B (cutRepresentative B ht r).val.2 z ∧
          @LT.lt _ oT.toLT ((cutPairIntoTriple B ht _ q t z).point
            (cutPairLeft B ht _ q t)) middle ∧
          @LT.lt _ oT.toLT middle ((cutPairIntoTriple B ht _ q t z).point
            (cutPairRight B ht _ q t)) := by
  let D := (cutRepresentative B ht r).val
  let J := fullMIOfNamed B D.1 D.2
  obtain ⟨z,hqz,hzt,fresh,hT⟩ := actual_reset_closed_pair_witness B ht J m q t hparent
  let P := cutPairStructure B ht D q t
  let T := cutTripleStructure B ht D q t z
  have hP := cutPair_mem B ht D q t
  let e : P.Embedding T := cutPairIntoTriple B ht D q t z
  let left : HiddenCutCarrier B ht P D := ⟨cutPairLeft B ht D q t,rfl⟩
  let right : HiddenCutCarrier B ht P D := ⟨cutPairRight B ht D q t,rfl⟩
  let middle : HiddenCutCarrier B ht T D :=
    ⟨⟨namedNode B D.2 z,(Target B ht).subset_closure _ (by simp)⟩,rfl⟩
  have fresh' : middle.val ∉ Set.range e.point := by
    rintro ⟨p,hp⟩
    have hv : p.val = namedNode B D.2 z := congrArg (fun x => x.val) hp
    apply fresh
    change namedNode B D.2 z ∈ cutPairSet B ht D q t
    rw [← hv]
    exact p.property
  let inc : T.Embedding (Target B ht) := (Target B ht).inclusion
    (cutTripleSet B ht D q t z) ((Target B ht).isClosed_closure _)
  have beforeParent : (actualCutSystem B ht T hT.1).parent D
      ((cutGeometryMap B ht hP.1 hT.1 e).point D left) middle := by
    apply (actualCutSystem_parent_realization B ht T hT.1 inc D _ _ q z rfl rfl).mpr
    exact m.inside_parent hqz
  have afterParent : (actualCutSystem B ht T hT.1).parent D middle
      ((cutGeometryMap B ht hP.1 hT.1 e).point D right) := by
    apply (actualCutSystem_parent_realization B ht T hT.1 inc D _ _ z t rfl rfl).mpr
    exact m.inside_parent hzt
  obtain ⟨oT,fixedT,keeps,before,after⟩ := normalized_midpoint_order_extension B ht priority
    hP.1 hT.1 hP.2 hT.2 e oP fixed r left right middle fresh'
    beforeParent afterParent comparison
  exact ⟨z,hqz,hzt,fresh,hT,oT,fixedT,keeps,middle.val,rfl,before,after⟩

end
end CCO.UnfilteredEP
