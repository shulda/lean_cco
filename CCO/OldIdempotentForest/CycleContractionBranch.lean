import CCO.GuardedTwoRoot.PrivateCycleClassification

/-! A positive simple arc between consecutive OLD roots follows one
specified original private branch in exactly one of its two orientations.
The conclusion records every original position, not just an endpoint pair
or a semigroup value. -/

universe u v w z
namespace CCO.OldIdempotentForest.CycleGeometry

open CCO.GuardedTwoRoot

variable {Roots : Type u} {Gadgets : Type v} {Branches : Type w} {V : Type z}
variable (P : PrivateBranchSystem Roots Gadgets Branches V)

structure RootFreePath where
  length : Nat
  positive : 0 < length
  vertex : Fin (length + 1) ↪ V
  adjacent : ∀ k : Fin length, P.graph.Adj (vertex k.castSucc) (vertex k.succ)
  left : Roots
  right : Roots
  first : vertex ⟨0,by omega⟩ = P.root left
  last : vertex ⟨length,by omega⟩ = P.root right
  no_internal_root : ∀ k : Fin (length + 1), 0 < k.val → k.val < length →
    ∀ r, vertex k ≠ P.root r

namespace RootFreePath
variable {P} (Q : RootFreePath P)

/-- Once the first genuine edge and its orientation are fixed, simplicity
forbids backtracking at each degree-two private interior. -/
theorem follow_first_branch (b : Branches)
    (first second : Fin (P.length b + 1))
    (hfirst : Q.vertex ⟨0,by have := Q.positive; omega⟩ = P.vertex b first)
    (hsecond : Q.vertex ⟨1,by have := Q.positive; omega⟩ = P.vertex b second)
    (hadj : P.PositionAdjacent b first second)
    (forward : Bool) (hstart : first.val = if forward then 0 else P.length b) :
    ∀ d (hd : d ≤ Q.length),
      ∃ q : Fin (P.length b + 1), d ≤ P.length b ∧
        q.val = (if forward then d else P.length b - d) ∧
        Q.vertex ⟨d,by omega⟩ = P.vertex b q := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro hd
    cases d with
    | zero =>
      refine ⟨first,Nat.zero_le _,?_,hfirst⟩
      simpa using hstart
    | succ k =>
      by_cases hk : k = 0
      · subst k
        refine ⟨second,P.positive b,?_,hsecond⟩
        have ha := hadj
        change first.val + 1 = second.val ∨ second.val + 1 = first.val at ha
        have hs := second.isLt
        cases forward with
        | false =>
          change first.val = P.length b at hstart
          change second.val = P.length b - 1
          omega
        | true =>
          change first.val = 0 at hstart
          change second.val = 1
          omega
      · obtain ⟨current,hklen,hcurrent,hcurrentPoint⟩ := ih k (by omega) (by omega)
        obtain ⟨previous,hprevlen,hprevious,hpreviousPoint⟩ := ih (k-1) (by omega) (by omega)
        have hcurrent0 : current.val ≠ 0 := by
          intro hz
          obtain ⟨r,hr⟩ := (P.branch_vertex_root_iff b current).mpr (Or.inl hz)
          exact Q.no_internal_root ⟨k,by omega⟩ (by change 0 < k; omega) (by change k < Q.length; omega) r
            (hcurrentPoint.trans hr)
        have hcurrentEnd : current.val ≠ P.length b := by
          intro hz
          obtain ⟨r,hr⟩ := (P.branch_vertex_root_iff b current).mpr (Or.inr hz)
          exact Q.no_internal_root ⟨k,by omega⟩ (by change 0 < k; omega) (by change k < Q.length; omega) r
            (hcurrentPoint.trans hr)
        have hcBound := current.isLt
        have hstep := Q.adjacent ⟨k,by omega⟩
        change P.graph.Adj (Q.vertex ⟨k,by omega⟩) (Q.vertex ⟨k+1,by omega⟩) at hstep
        rw [hcurrentPoint] at hstep
        obtain ⟨next,hnext,hnextPoint⟩ := P.interior_neighbours b current
          (by omega) (by omega) _ hstep
        have hnotBack : next ≠ previous := by
          intro he
          have hv : Q.vertex ⟨k+1,by omega⟩ = Q.vertex ⟨k-1,by omega⟩ :=
            hnextPoint.symm.trans ((congrArg (P.vertex b) he).trans hpreviousPoint.symm)
          have hn := congrArg Fin.val (Q.vertex.injective hv)
          change k+1 = k-1 at hn
          omega
        have hnotVal : next.val ≠ previous.val := fun he => hnotBack (Fin.ext he)
        change current.val + 1 = next.val ∨ next.val + 1 = current.val at hnext
        have hdlen : k+1 ≤ P.length b := by
          cases forward <;> simp at hcurrent hprevious ⊢ <;> omega
        refine ⟨next,hdlen,?_,hnextPoint.symm⟩
        cases forward <;> simp at hcurrent hprevious ⊢ <;> omega

structure OriginalBranchTraversal where
  branch : Branches
  forward : Bool
  length_eq : Q.length = P.length branch
  position : Fin (Q.length + 1) ↪ Fin (P.length branch + 1)
  rank : ∀ d, (position d).val = if forward then d.val else P.length branch - d.val
  point : ∀ d, Q.vertex d = P.vertex branch (position d)
  left_eq : Q.left = if forward then P.left (P.owner branch) else P.right (P.owner branch)
  right_eq : Q.right = if forward then P.right (P.owner branch) else P.left (P.owner branch)

theorem original_branch_traversal : Nonempty Q.OriginalBranchTraversal := by
  classical
  let zero : Fin Q.length := ⟨0,Q.positive⟩
  obtain ⟨edge⟩ := P.branch_edge_witness (Q.adjacent zero)
  have hs : Q.vertex ⟨0,by have := Q.positive; omega⟩ = P.vertex edge.branch edge.source := edge.source_eq.symm
  have ht : Q.vertex ⟨1,by have := Q.positive; omega⟩ = P.vertex edge.branch edge.target := edge.target_eq.symm
  have hsourceRoot : P.vertex edge.branch edge.source = P.root Q.left := edge.source_eq.trans Q.first
  obtain hzero | hend := (P.branch_vertex_root_iff edge.branch edge.source).mp ⟨Q.left,hsourceRoot⟩
  · let forward : Bool := true
    have htrack := Q.follow_first_branch edge.branch edge.source edge.target hs ht edge.adjacent forward hzero
    have hlength : Q.length = P.length edge.branch := by
      obtain ⟨last,hlen,hrank,hpoint⟩ := htrack Q.length (Nat.le_refl _)
      obtain h0 | he := (P.branch_vertex_root_iff edge.branch last).mp ⟨Q.right,hpoint.symm.trans Q.last⟩
      · have := Q.positive
        simp [forward] at hrank
        omega
      · simpa [forward,he] using hrank.symm
    let pos (d : Fin (Q.length+1)) : Fin (P.length edge.branch+1) := (htrack d.val (by omega)).choose
    have hpos (d : Fin (Q.length+1)) := (htrack d.val (by omega)).choose_spec
    have hrank (d : Fin (Q.length+1)) : (pos d).val = if forward then d.val else P.length edge.branch-d.val := (hpos d).2.1
    have hpoint (d : Fin (Q.length+1)) : Q.vertex d = P.vertex edge.branch (pos d) := (hpos d).2.2
    refine ⟨{
      branch := edge.branch
      forward := forward
      length_eq := hlength
      position := ⟨pos,?_⟩
      rank := hrank
      point := hpoint
      left_eq := ?_
      right_eq := ?_ }⟩
    · intro a b hab
      apply Fin.ext
      have he := congrArg Fin.val hab
      have ha := hrank a
      have hb := hrank b
      simp [forward] at ha hb
      omega
    · have hp : pos ⟨0,by omega⟩ = ⟨0,Nat.succ_pos _⟩ := Fin.ext (by simpa [forward] using hrank ⟨0,by omega⟩)
      apply P.root.injective
      exact Q.first.symm.trans ((hpoint ⟨0,by omega⟩).trans (hp ▸ P.first edge.branch))
    · have hp : pos ⟨Q.length,by omega⟩ = ⟨P.length edge.branch,Nat.lt_succ_self _⟩ := Fin.ext (by simpa [forward,hlength] using hrank ⟨Q.length,by omega⟩)
      apply P.root.injective
      exact Q.last.symm.trans ((hpoint ⟨Q.length,by omega⟩).trans (hp ▸ P.last edge.branch))
  · let forward : Bool := false
    have htrack := Q.follow_first_branch edge.branch edge.source edge.target hs ht edge.adjacent forward hend
    have hlength : Q.length = P.length edge.branch := by
      obtain ⟨last,hlen,hrank,hpoint⟩ := htrack Q.length (Nat.le_refl _)
      obtain h0 | he := (P.branch_vertex_root_iff edge.branch last).mp ⟨Q.right,hpoint.symm.trans Q.last⟩
      · simp [forward,h0] at hrank
        omega
      · have := Q.positive
        simp [forward,he] at hrank
        omega
    let pos (d : Fin (Q.length+1)) : Fin (P.length edge.branch+1) := (htrack d.val (by omega)).choose
    have hpos (d : Fin (Q.length+1)) := (htrack d.val (by omega)).choose_spec
    have hrank (d : Fin (Q.length+1)) : (pos d).val = if forward then d.val else P.length edge.branch-d.val := (hpos d).2.1
    have hpoint (d : Fin (Q.length+1)) : Q.vertex d = P.vertex edge.branch (pos d) := (hpos d).2.2
    refine ⟨{
      branch := edge.branch
      forward := forward
      length_eq := hlength
      position := ⟨pos,?_⟩
      rank := hrank
      point := hpoint
      left_eq := ?_
      right_eq := ?_ }⟩
    · intro a b hab
      apply Fin.ext
      have ha := a.isLt
      have hb := b.isLt
      have he := congrArg Fin.val hab
      have hpa := hrank a
      have hpb := hrank b
      simp [forward] at hpa hpb
      omega
    · have hp : pos ⟨0,by omega⟩ = ⟨P.length edge.branch,Nat.lt_succ_self _⟩ := Fin.ext (by simpa [forward] using hrank ⟨0,by omega⟩)
      apply P.root.injective
      exact Q.first.symm.trans ((hpoint ⟨0,by omega⟩).trans (hp ▸ P.last edge.branch))
    · have hp : pos ⟨Q.length,by omega⟩ = ⟨0,Nat.succ_pos _⟩ := Fin.ext (by simpa [forward,hlength] using hrank ⟨Q.length,by omega⟩)
      apply P.root.injective
      exact Q.last.symm.trans ((hpoint ⟨Q.length,by omega⟩).trans (hp ▸ P.first edge.branch))

end RootFreePath
end CCO.OldIdempotentForest.CycleGeometry
