import CCO.TypedOrbitFrames.ChordHomGlue
import Lean.Elab.Tactic.Omega

/-!
# B053 C04: genuine finite index geometry for a specified chord split

For a simple old specified cycle with n vertices, a chord between
positions 0 and k is proper exactly when 2 <= k and k+2 <= n.
Its two arcs have respectively k+1 and n-k+1 distinct vertices,
BOTH strictly fewer than n. The chord itself closes the two arcs.

This file constructs the ACTUAL Fin-index injections, proves their
images cover every original cycle vertex and intersect only at
the two actual chord endpoints 0 and k, and checks both endpoint
orders (left 0→k, right k→0). These are the missing concrete
combinatorial premises for the later C04 old-SAP image gluing;
neither a realizability hypothesis nor any extra original
source theorem is invented here.
-/

namespace CCO.TypedOrbitFrames

/-- A genuine non-adjacent chord between positions 0 and k on
a simple n-cycle, with at least two OLD cycle edges on EACH arc. -/
structure OriginalChordCut (n k : Nat) : Prop where
  left_nontrivial : 2 ≤ k
  right_nontrivial : k + 2 ≤ n

/-- Left cycle arc: vertices 0,1,...,k. The chord closes k→0. -/
def originalChordLeftIndex {n k : Nat}
    (cut : OriginalChordCut n k) (a : Fin (k + 1)) : Fin n :=
  ⟨a.val, by have := a.isLt; omega⟩

/-- Right cycle arc: vertices k,k+1,...,n-1,0. The chord closes 0→k.
The last index wraps to the ACTUAL original 0; it is not a duplicate
interior vertex. -/
def originalChordRightIndex {n k : Nat}
    (cut : OriginalChordCut n k) (b : Fin (n - k + 1)) : Fin n :=
  if h : b.val < n - k then
    ⟨k + b.val, by have := cut.right_nontrivial; omega⟩
  else
    ⟨0, by have := cut.right_nontrivial; omega⟩

/-- Both subcycles are strictly shorter than the old cycle.
This is the exact well-founded measure used by source11 C04. -/
theorem original_chord_both_cycles_shorter {n k : Nat}
    (cut : OriginalChordCut n k) :
    k + 1 < n ∧ n - k + 1 < n := by
  constructor
  · omega
  · omega

/-- The actual left arc does not identify two old cycle positions. -/
theorem original_chord_left_injective {n k : Nat}
    (cut : OriginalChordCut n k) :
    Function.Injective (originalChordLeftIndex cut) := by
  intro a b h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simpa only [originalChordLeftIndex, Fin.val_mk] using hv

/-- The right arc is injective even though its LAST vertex
wraps to actual original index zero. -/
theorem original_chord_right_injective {n k : Nat}
    (cut : OriginalChordCut n k) :
    Function.Injective (originalChordRightIndex cut) := by
  intro a b h
  apply Fin.ext
  have hv := congrArg Fin.val h
  have ha := a.isLt
  have hb := b.isLt
  unfold originalChordRightIndex at hv
  split_ifs at hv <;> simp only [Fin.val_mk] at hv <;> omega

/-- The old zero index is the first left endpoint. -/
theorem original_chord_left_zero {n k : Nat}
    (cut : OriginalChordCut n k) :
    originalChordLeftIndex cut ⟨0, by omega⟩ =
      (⟨0, by omega⟩ : Fin n) := rfl

/-- The old k index is the last left endpoint. -/
theorem original_chord_left_last {n k : Nat}
    (cut : OriginalChordCut n k) :
    originalChordLeftIndex cut ⟨k, by omega⟩ =
      (⟨k, by omega⟩ : Fin n) := rfl

/-- The old k index is the first right endpoint. -/
theorem original_chord_right_zero {n k : Nat}
    (cut : OriginalChordCut n k) :
    originalChordRightIndex cut ⟨0, by omega⟩ =
      (⟨k, by omega⟩ : Fin n) := by
  apply Fin.ext
  have h : 0 < n - k := by omega
  simp [originalChordRightIndex, h]

/-- The old zero index is the LAST right endpoint, in precisely
the opposite chord orientation to the left arc. -/
theorem original_chord_right_last {n k : Nat}
    (cut : OriginalChordCut n k) :
    originalChordRightIndex cut ⟨n - k, by omega⟩ =
      (⟨0, by omega⟩ : Fin n) := by
  apply Fin.ext
  simp [originalChordRightIndex]

/-- Each old cycle vertex belongs to one of the two REAL
subcycle arcs (including the shared 0 and k positions). -/
theorem original_chord_arc_cover {n k : Nat}
    (cut : OriginalChordCut n k) (j : Fin n) :
    (∃ a : Fin (k + 1), originalChordLeftIndex cut a = j) ∨
    (∃ b : Fin (n - k + 1), originalChordRightIndex cut b = j) := by
  by_cases hj : j.val ≤ k
  · left
    refine ⟨⟨j.val, by omega⟩, ?_⟩
    apply Fin.ext
    rfl
  · right
    let b : Fin (n - k + 1) := ⟨j.val - k, by omega⟩
    refine ⟨b, ?_⟩
    have hb : b.val < n - k := by
      dsimp [b]
      omega
    apply Fin.ext
    simp [originalChordRightIndex, hb, b]
    omega

/-- The ONLY common old cycle vertices of the two actual arc
injections are the two specified chord endpoints; this protects
the exact two-point SAP overlap rather than silently aligning
extra old source vertices. -/
theorem original_chord_arc_intersection_endpoints {n k : Nat}
    (cut : OriginalChordCut n k)
    (a : Fin (k + 1)) (b : Fin (n - k + 1))
    (hab : originalChordLeftIndex cut a =
      originalChordRightIndex cut b) :
    (originalChordLeftIndex cut a).val = 0 ∨
      (originalChordLeftIndex cut a).val = k := by
  have hv := congrArg Fin.val hab
  by_cases hb : b.val < n - k
  · right
    simp only [originalChordLeftIndex,
      originalChordRightIndex, dif_pos hb, Fin.val_mk] at hv ⊢
    have ha := a.isLt
    omega
  · left
    simp only [originalChordLeftIndex,
      originalChordRightIndex, dif_neg hb, Fin.val_mk] at hv ⊢
    exact hv

end CCO.TypedOrbitFrames
