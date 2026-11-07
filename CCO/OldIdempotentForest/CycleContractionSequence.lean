import CCO.OldIdempotentForest.CycleContractionRotation
import CCO.OldIdempotentForest.CycleContractionCuts
import CCO.OldIdempotentForest.CycleContractionBranch

/-! An actual specified private-branch cycle supplies a finite ordered
sequence of all its OLD-root occurrences. The arcs are constructed from
consecutive original occurrence cuts; their ordered intervals cover the
entire original cycle, and each arc has no interior OLD root. -/

universe u v w z
namespace CCO.OldIdempotentForest.CycleGeometry

open CCO.GuardedTwoRoot

variable {Roots : Type u} {Gadgets : Type v} {Branches : Type w} {V : Type z}
variable {P : PrivateBranchSystem Roots Gadgets Branches V}

def oldRootMark (C : P.Cycle) (start : Fin C.length) (distance : Nat) : Prop :=
  ∃ r : Roots, P.root r = C.vertex (cycleShift C.positive start distance)

/-- Consecutive actual OLD-root cuts give one literal simple original
cycle arc. Its positive length is strictly less than the cycle length. -/
def cycleRootArc (C : P.Cycle) (start : Fin C.length)
    (cuts : OrderedCuts C.length (oldRootMark C start))
    (root : Fin (cuts.count + 1) → Roots)
    (hroot : ∀ i, P.root (root i) = C.vertex (cycleShift C.positive start (cuts.cut i)))
    (i : Fin cuts.count) : RootFreePath P where
  length := cuts.cut i.succ - cuts.cut i.castSucc
  positive := cuts.adjacent_length_pos i
  vertex := {
    toFun := fun d => C.vertex (cycleShift C.positive start (cuts.cut i.castSucc + d.val))
    inj' := by
      intro a b heq
      have ha := a.isLt
      have hb := b.isLt
      have hlength := cuts.adjacent_length_lt i
      have hindex := C.vertex.injective heq
      rw [cycleShift_add,cycleShift_add] at hindex
      apply Fin.ext
      exact cycleShift_injective_lt C.positive
        (cycleShift C.positive start (cuts.cut i.castSucc)) a.val b.val
        (by omega) (by omega) hindex }
  adjacent := by
    intro k
    change P.graph.Adj
      (C.vertex (cycleShift C.positive start (cuts.cut i.castSucc + k.val)))
      (C.vertex (cycleShift C.positive start (cuts.cut i.castSucc + (k.val + 1))))
    rw [← Nat.add_assoc,cycleShift_succ]
    exact C.adjacent _
  left := root i.castSucc
  right := root i.succ
  first := by
    change C.vertex (cycleShift C.positive start (cuts.cut i.castSucc + 0)) = P.root (root i.castSucc)
    simpa only [Nat.add_zero] using (hroot i.castSucc).symm
  last := by
    change C.vertex (cycleShift C.positive start
      (cuts.cut i.castSucc + (cuts.cut i.succ - cuts.cut i.castSucc))) = P.root (root i.succ)
    have hsum : cuts.cut i.castSucc + (cuts.cut i.succ - cuts.cut i.castSucc) = cuts.cut i.succ := by
      have h := cuts.adjacent_positive i
      omega
    rw [hsum]
    exact (hroot i.succ).symm
  no_internal_root := by
    intro k hk0 hkEnd r heq
    change C.vertex (cycleShift C.positive start (cuts.cut i.castSucc + k.val)) = P.root r at heq
    have hleft : cuts.cut i.castSucc < cuts.cut i.castSucc + k.val := by omega
    have hright : cuts.cut i.castSucc + k.val < cuts.cut i.succ := by
      have h := cuts.adjacent_positive i
      omega
    exact cuts.no_inside i (cuts.cut i.castSucc + k.val) hleft hright ⟨r,heq.symm⟩

/-- This data is constructed from the ACTUAL specified cycle. The final
root repeats the first only to close the cyclic sequence; all initial
root occurrences are pairwise distinct ORIGINAL roots. -/
structure OrderedCycleSequence (C : P.Cycle) where
  start : Fin C.length
  cuts : OrderedCuts C.length (oldRootMark C start)
  root : Fin (cuts.count + 1) → Roots
  root_eq : ∀ i, P.root (root i) = C.vertex (cycleShift C.positive start (cuts.cut i))
  closed : root (Fin.last cuts.count) = root 0
  injective_initial : Function.Injective (fun i : Fin cuts.count => root i.castSucc)

namespace OrderedCycleSequence
variable {C : P.Cycle} (D : OrderedCycleSequence C)

def arc (i : Fin D.cuts.count) : RootFreePath P :=
  cycleRootArc C D.start D.cuts D.root D.root_eq i

theorem arc_length (i : Fin D.cuts.count) :
    (D.arc i).length = D.cuts.cut i.succ - D.cuts.cut i.castSucc := rfl

theorem arc_vertex (i : Fin D.cuts.count) (d : Fin ((D.arc i).length + 1)) :
    (D.arc i).vertex d = C.vertex (cycleShift C.positive D.start (D.cuts.cut i.castSucc + d.val)) := rfl

theorem arc_left (i : Fin D.cuts.count) : (D.arc i).left = D.root i.castSucc := rfl
theorem arc_right (i : Fin D.cuts.count) : (D.arc i).right = D.root i.succ := rfl

theorem arc_length_lt_cycle (i : Fin D.cuts.count) : (D.arc i).length < C.length :=
  D.cuts.adjacent_length_lt i

/-- The arc intervals retain every ORIGINAL edge occurrence exactly once
and in cyclic order, starting at the selected actual OLD root. -/
theorem original_indices :
    (List.range D.cuts.count).flatMap
      (fun i => List.range' (D.cuts.cutAt i) (D.cuts.cutAt (i + 1) - D.cuts.cutAt i)) =
      List.range C.length := D.cuts.original_indices

theorem original_cycle_index_order :
    ((List.range D.cuts.count).flatMap
      (fun i => List.range' (D.cuts.cutAt i) (D.cuts.cutAt (i + 1) - D.cuts.cutAt i))).map
        (cycleShift C.positive D.start) =
      (List.range C.length).map (cycleShift C.positive D.start) :=
  congrArg (List.map (cycleShift C.positive D.start)) D.original_indices

theorem original_cycle_vertex_order :
    ((List.range D.cuts.count).flatMap
      (fun i => List.range' (D.cuts.cutAt i) (D.cuts.cutAt (i + 1) - D.cuts.cutAt i))).map
        (fun d => C.vertex (cycleShift C.positive D.start d)) =
      (List.range C.length).map (fun d => C.vertex (cycleShift C.positive D.start d)) :=
  congrArg (List.map (fun d => C.vertex (cycleShift C.positive D.start d))) D.original_indices

end OrderedCycleSequence

/-- Actual ordered cycle contraction: two accepted OLD root occurrences
provide a start and an interior cut. Sorting ALL marked occurrences then
constructs the complete ordered arc sequence, with no contraction callback
or assumed macro traversal sequence. -/
theorem exists_ordered_cycle_sequence (C : P.Cycle) : Nonempty (OrderedCycleSequence C) := by
  classical
  obtain ⟨r,s,hrs,hr,hs⟩ := C.cycle_has_two_old_roots
  obtain ⟨start,hstart⟩ := hr
  obtain ⟨target,htarget⟩ := hs
  have htarget_ne : target ≠ start := by
    intro heq
    apply hrs
    apply P.root.injective
    exact hstart.symm.trans ((congrArg C.vertex heq).symm.trans htarget)
  have hzero : oldRootMark C start 0 := by
    exact ⟨r,by simpa only [cycleShift_zero] using hstart.symm⟩
  have hlast : oldRootMark C start C.length := by
    exact ⟨r,by simpa only [cycleShift_period] using hstart.symm⟩
  have hinterior : ∃ d, 0 < d ∧ d < C.length ∧ oldRootMark C start d := by
    obtain ⟨d,hd,hreach⟩ := cycleShift_reaches C.positive start target
    have hpos : 0 < d := by
      by_contra h
      have hz : d = 0 := by omega
      have ht : target = start := by simpa only [hz,cycleShift_zero] using hreach.symm
      exact htarget_ne ht
    refine ⟨d,hpos,hd,s,?_⟩
    rw [hreach]
    exact htarget.symm
  obtain ⟨cuts⟩ := exists_orderedCuts C.length (oldRootMark C start) C.positive hzero hlast hinterior
  have hmarked (i : Fin (cuts.count + 1)) :
      ∃ r : Roots, P.root r = C.vertex (cycleShift C.positive start (cuts.cut i)) := cuts.marked i
  let root (i : Fin (cuts.count + 1)) : Roots := Classical.choose (hmarked i)
  have hroot (i : Fin (cuts.count + 1)) :
      P.root (root i) = C.vertex (cycleShift C.positive start (cuts.cut i)) :=
    Classical.choose_spec (hmarked i)
  have hclosed : root (Fin.last cuts.count) = root 0 := by
    have hfirst := hroot 0
    have hlast' := hroot (Fin.last cuts.count)
    rw [cuts.first,cycleShift_zero] at hfirst
    rw [cuts.last,cycleShift_period] at hlast'
    exact P.root.injective (hlast'.trans hfirst.symm)
  have hinjective : Function.Injective (fun i : Fin cuts.count => root i.castSucc) := by
    intro i j hij
    have hpoints := congrArg P.root hij
    rw [hroot,hroot] at hpoints
    have hshift := C.vertex.injective hpoints
    have hcuts := cycleShift_injective_lt C.positive start (cuts.cut i.castSucc) (cuts.cut j.castSucc)
      (cuts.initial_cut_lt i) (cuts.initial_cut_lt j) hshift
    exact Fin.ext (congrArg (fun q : Fin (cuts.count+1) => q.val) (cuts.cut.injective hcuts))
  exact ⟨{
    start := start
    cuts := cuts
    root := root
    root_eq := hroot
    closed := hclosed
    injective_initial := hinjective }⟩

end CCO.OldIdempotentForest.CycleGeometry
