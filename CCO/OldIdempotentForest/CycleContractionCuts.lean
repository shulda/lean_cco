import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Range
import Lean.Elab.Tactic.Omega

/-! Canonical increasing enumeration of all marked original cycle
positions, including the two linear boundary occurrences. Consecutive
cuts have no marked interior occurrence and delimit positive intervals.
This is a finite construction, not a supplied contraction provider. -/

namespace CCO.OldIdempotentForest.CycleGeometry

noncomputable def markedCuts (n : Nat) (mark : Nat → Prop) : Finset Nat := by
  classical
  exact (Finset.range (n + 1)).filter mark

theorem mem_markedCuts (n : Nat) (mark : Nat → Prop) (i : Nat) :
    i ∈ markedCuts n mark ↔ i ≤ n ∧ mark i := by
  classical
  simp only [markedCuts,Finset.mem_filter,Finset.mem_range,Nat.lt_succ_iff]

/-- The count is the number of positive root-to-root arcs. Both boundary
occurrences are retained, so there is one more cut than arc. -/
structure OrderedCuts (n : Nat) (mark : Nat → Prop) where
  count : Nat
  two : 2 ≤ count
  cut : Fin (count + 1) ↪o Nat
  first : cut 0 = 0
  last : cut (Fin.last count) = n
  marked : ∀ i, mark (cut i)
  complete : ∀ j, j ≤ n → mark j → ∃ i, cut i = j

/-- Actual sorted finite-set enumeration supplies all cuts. An interior
marked occurrence guarantees at least two arcs, rather than one loop. -/
theorem exists_orderedCuts (n : Nat) (mark : Nat → Prop) (hn : 0 < n)
    (hzero : mark 0) (hlast : mark n)
    (hinterior : ∃ j, 0 < j ∧ j < n ∧ mark j) :
    Nonempty (OrderedCuts n mark) := by
  classical
  let cuts := markedCuts n mark
  obtain ⟨j,hj0,hjn,hj⟩ := hinterior
  have h0j : 0 ≠ j := by omega
  have h0n : 0 ≠ n := by omega
  have hjn' : j ≠ n := by omega
  have hthree : ({0,j,n} : Finset Nat).card = 3 := by simp [h0j,h0n,hjn']
  have hsubset : ({0,j,n} : Finset Nat) ⊆ cuts := by
    have hzmem : 0 ∈ cuts := (mem_markedCuts n mark 0).mpr ⟨by omega,hzero⟩
    have hjmem : j ∈ cuts := (mem_markedCuts n mark j).mpr ⟨by omega,hj⟩
    have hnmem : n ∈ cuts := (mem_markedCuts n mark n).mpr ⟨le_rfl,hlast⟩
    intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with hx | hx | hx
    · exact hx.symm ▸ hzmem
    · exact hx.symm ▸ hjmem
    · exact hx.symm ▸ hnmem
  have hcard : 3 ≤ cuts.card := by
    have h := Finset.card_le_card hsubset
    omega
  let m := cuts.card - 1
  have hm : 2 ≤ m := by dsimp [m]; omega
  have hsize : cuts.card = m + 1 := by dsimp [m]; omega
  let e : Fin (m + 1) ↪o Nat := cuts.orderEmbOfFin hsize
  have emem (i : Fin (m + 1)) : e i ∈ cuts := cuts.orderEmbOfFin_mem hsize i
  have ebound (i : Fin (m + 1)) : e i ≤ n :=
    ((mem_markedCuts n mark (e i)).mp (emem i)).1
  have esurj (x : Nat) (hx : x ∈ cuts) : ∃ i, e i = x := by
    obtain ⟨i,hi⟩ := (cuts.orderIsoOfFin hsize).surjective ⟨x,hx⟩
    exact ⟨i,congrArg Subtype.val hi⟩
  have hfirst : e 0 = 0 := by
    obtain ⟨i,hi⟩ := esurj 0 ((mem_markedCuts n mark 0).mpr ⟨by omega,hzero⟩)
    have hle : (0 : Fin (m + 1)) ≤ i := by change 0 ≤ i.val; omega
    have hmono := e.monotone hle
    omega
  have hlast' : e (Fin.last m) = n := by
    obtain ⟨i,hi⟩ := esurj n ((mem_markedCuts n mark n).mpr ⟨le_rfl,hlast⟩)
    have hmono := e.monotone (Fin.le_last i)
    have hb := ebound (Fin.last m)
    omega
  exact ⟨{
    count := m
    two := hm
    cut := e
    first := hfirst
    last := hlast'
    marked := fun i => ((mem_markedCuts n mark (e i)).mp (emem i)).2
    complete := fun x hx hm => esurj x ((mem_markedCuts n mark x).mpr ⟨hx,hm⟩) }⟩

namespace OrderedCuts
variable {n : Nat} {mark : Nat → Prop} (C : OrderedCuts n mark)

theorem bounds (i : Fin (C.count + 1)) : C.cut i ≤ n := by
  calc
    C.cut i ≤ C.cut (Fin.last C.count) := C.cut.monotone (Fin.le_last i)
    _ = n := C.last

theorem adjacent_positive (i : Fin C.count) : C.cut i.castSucc < C.cut i.succ :=
  C.cut.strictMono Fin.castSucc_lt_succ

theorem initial_cut_lt (i : Fin C.count) : C.cut i.castSucc < n := by
  have hlt : i.castSucc < Fin.last C.count := by change i.val < C.count; exact i.isLt
  simpa only [C.last] using C.cut.strictMono hlt

theorem final_cut_pos (i : Fin C.count) : 0 < C.cut i.succ := by
  have hlt : (0 : Fin (C.count + 1)) < i.succ := by change 0 < i.val + 1; omega
  simpa only [C.first] using C.cut.strictMono hlt

theorem adjacent_length_pos (i : Fin C.count) :
    0 < C.cut i.succ - C.cut i.castSucc := Nat.sub_pos_of_lt (C.adjacent_positive i)

/-- There is no intervening OLD root occurrence between successive cuts. -/
theorem no_inside (i : Fin C.count) (j : Nat)
    (hleft : C.cut i.castSucc < j) (hright : j < C.cut i.succ) : ¬ mark j := by
  intro hj
  have hjn : j ≤ n := by have h := C.bounds i.succ; omega
  obtain ⟨q,hq⟩ := C.complete j hjn hj
  have hlow : i.val < q.val := by
    by_contra h
    have hle : q ≤ i.castSucc := by change q.val ≤ i.val; omega
    have hc := C.cut.monotone hle
    rw [hq] at hc
    omega
  have hhigh : q.val < i.val + 1 := by
    by_contra h
    have hle : i.succ ≤ q := by change i.val + 1 ≤ q.val; omega
    have hc := C.cut.monotone hle
    rw [hq] at hc
    omega
  omega

/-- At least two arcs and the retained outer endpoints exclude an arc
whose length equals the whole original cycle. -/
theorem adjacent_length_lt (i : Fin C.count) :
    C.cut i.succ - C.cut i.castSucc < n := by
  have htwo := C.two
  have hright := C.bounds i.succ
  have hadj := C.adjacent_positive i
  by_cases hi : i.val = 0
  · have hlt : i.succ < Fin.last C.count := by change i.val + 1 < C.count; omega
    have hc := C.cut.strictMono hlt
    rw [C.last] at hc
    omega
  · have hlt : (0 : Fin (C.count + 1)) < i.castSucc := by change 0 < i.val; omega
    have hc := C.cut.strictMono hlt
    rw [C.first] at hc
    omega

/-- Extend the cut sequence constantly after its last element. This is
only a convenient natural-indexed presentation of the same finite cuts. -/
def cutAt (j : Nat) : Nat := C.cut ⟨min j C.count,by omega⟩

theorem cutAt_of_le (j : Nat) (hj : j ≤ C.count) : C.cutAt j = C.cut ⟨j,by omega⟩ := by
  apply congrArg C.cut
  apply Fin.ext
  exact Nat.min_eq_left hj

theorem cutAt_monotone : Monotone C.cutAt := by
  intro i j hij
  apply C.cut.monotone
  change min i C.count ≤ min j C.count
  omega

@[simp] theorem cutAt_zero : C.cutAt 0 = 0 := by
  rw [cutAt_of_le _ _ (Nat.zero_le _)]
  exact C.first

@[simp] theorem cutAt_last : C.cutAt C.count = n := by
  rw [cutAt_of_le _ _ le_rfl]
  exact C.last

end OrderedCuts

/-- Adjacent natural intervals concatenate to their entire outer span.
No assumption of transitivity of a macro relation is involved. -/
theorem adjacent_ranges_partition (cut : Nat → Nat) (hmono : Monotone cut) (m : Nat) :
    (List.range m).flatMap (fun i => List.range' (cut i) (cut (i + 1) - cut i)) =
      List.range' (cut 0) (cut m - cut 0) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ,List.flatMap_append,List.flatMap_singleton,ih]
    have h0m : cut 0 ≤ cut m := hmono (Nat.zero_le _)
    have hm : cut m ≤ cut (m + 1) := hmono (Nat.le_succ _)
    have hstart : cut 0 + (cut m - cut 0) = cut m := by omega
    calc
      List.range' (cut 0) (cut m - cut 0) ++ List.range' (cut m) (cut (m + 1) - cut m) =
          List.range' (cut 0) (cut m - cut 0) ++
            List.range' (cut 0 + (cut m - cut 0)) (cut (m + 1) - cut m) := by rw [hstart]
      _ = List.range' (cut 0) ((cut m - cut 0) + (cut (m + 1) - cut m)) :=
        List.range'_append_1
      _ = List.range' (cut 0) (cut (m + 1) - cut 0) := by
        congr 1
        omega

/-- Every original edge index appears EXACTLY once and in its original
order in the consecutive cut intervals. -/
theorem OrderedCuts.original_indices {n : Nat} {mark : Nat → Prop} (C : OrderedCuts n mark) :
    (List.range C.count).flatMap
      (fun i => List.range' (C.cutAt i) (C.cutAt (i + 1) - C.cutAt i)) = List.range n := by
  rw [adjacent_ranges_partition C.cutAt C.cutAt_monotone,C.cutAt_zero,C.cutAt_last]
  simp [List.range_eq_range']

end CCO.OldIdempotentForest.CycleGeometry
