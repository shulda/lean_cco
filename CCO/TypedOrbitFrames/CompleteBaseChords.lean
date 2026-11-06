import CCO.ParityHasse.Sparse.Cycles
import Mathlib.Combinatorics.SimpleGraph.Basic
import Lean.Elab.Tactic.Omega

/-!
# B053 T01: long chordless cycles cannot meet a complete real base

The pinned source11 starts with a COMPLETE old real base D. All
distinct pairs in D have actual old diversity colours, and every
new clone has a prescribed old atomic spoke to EVERY base vertex.
Consequently in the graph of *specified* edges, every base vertex
is adjacent to every other vertex.

A cycle of length at least four containing any base vertex has a
specified chord to the vertex two steps later on the cycle. This
does not assert that clone-clone nonedges are coloured and does not
use a hidden SAP or an HN theorem. Later stages must separately
prove that shorter compatible OLD cycles can be glued using actual
old homogeneity/SAP and then apply original semantic HOM CCO.
-/

namespace CCO.TypedOrbitFrames

open CCO.ParityHasse.Sparse

universe u v
variable {D : Type u} {X : Type v}

/-- The underlying SPECIFIED graph of a complete old real base
with all real-base-to-clone spokes present. The graph contains a
specified diversity edge between every distinct pair touching D.
The clone-only graph can have arbitrary missing edges. -/
def CompleteBaseSpokes (G : SimpleGraph (D ⊕ X)) : Prop :=
  ∀ (d : D) (z : D ⊕ X), z ≠ Sum.inl d →
    G.Adj (Sum.inl d) z

/-- A necessary condition on every chordless simple cycle of
length at least four: no edge may connect positions two apart.
The stronger all-chords-free condition implies this predicate. -/
def NoTwoStepChords {n : Nat} [NeZero n]
    (G : SimpleGraph (D ⊕ X)) (f : CycleCode (D ⊕ X) n) : Prop :=
  4 ≤ n → ∀ i : ZMod n, ¬ G.Adj (f i) (f (i + 2))

/-- Positions i and i+2 are distinct on every cycle with n≥4.
In particular a distance-two edge is a genuine chord, not an
old positive identity. -/
theorem cycle_two_steps_ne_self {n : Nat} [NeZero n]
    (hn : 4 ≤ n) (i : ZMod n) : i + 2 ≠ i := by
  intro h
  have h0 : i + (2 : ZMod n) = i + 0 := by
    simpa only [add_zero] using h
  have h2 : (2 : ZMod n) = 0 := add_left_cancel h0
  exact zmod_two_ne_zero (by omega : 3 ≤ n) h2

/-- EVERY base vertex of a cyclic injective code of length≥4 has
a genuinely specified chord at distance two. It suffices that
all base/base and base/clone old edges were specified. -/
theorem complete_base_forces_two_step_chord
    {n : Nat} [NeZero n]
    (hn : 4 ≤ n)
    (G : SimpleGraph (D ⊕ X))
    (hBase : CompleteBaseSpokes G)
    (f : CycleCode (D ⊕ X) n)
    (i : ZMod n) (d : D)
    (hi : f i = Sum.inl d) :
    G.Adj (f i) (f (i + 2)) := by
  have hneq : f (i + 2) ≠ Sum.inl d := by
    intro h
    have hf : f (i + 2) = f i := h.trans hi.symm
    exact cycle_two_steps_ne_self hn i (f.injective hf)
  simpa only [hi] using hBase d (f (i + 2)) hneq

/-- C01–C02 base-chord firewall: an injective specified cycle
with no distance-two chords and length≥4 cannot contain ANY
old real base vertex. Thus every such chordless cycle is
entirely a clone-only cycle, independently of the internal
clone graph H. -/
theorem complete_base_chordless_cycle_clone_only
    {n : Nat} [NeZero n]
    (hn : 4 ≤ n)
    (G : SimpleGraph (D ⊕ X))
    (hBase : CompleteBaseSpokes G)
    (f : CycleCode (D ⊕ X) n)
    (hNo : NoTwoStepChords G f) :
    ∀ i : ZMod n, ∃ x : X, f i = Sum.inr x := by
  intro i
  cases h : f i with
  | inl d =>
      exact False.elim
        (hNo hn i (complete_base_forces_two_step_chord
          hn G hBase f i d h))
  | inr x =>
      exact ⟨x, rfl⟩


/-- Source11 C01/C02 in exactly the long-vs-triangle form:
if a specified simple cycle of length at least three meets
the old complete base and has NO chords, then it has length
exactly three. The weakened test only excludes distance-two
chords for length at least four; for an actual triangle it is
vacuously satisfied, since its distance-two edge is a SIDE,
not a chord. -/
theorem complete_base_chordless_meeting_base_is_triangle
    {n : Nat} [NeZero n]
    (hn : 3 ≤ n)
    (G : SimpleGraph (D ⊕ X))
    (hBase : CompleteBaseSpokes G)
    (f : CycleCode (D ⊕ X) n)
    (hNo : NoTwoStepChords G f)
    (hTouches : ∃ i : ZMod n, ∃ d : D, f i = Sum.inl d) :
    n = 3 := by
  by_contra hneq
  have h4 : 4 ≤ n := by omega
  obtain ⟨i, d, hi⟩ := hTouches
  exact hNo h4 i
    (complete_base_forces_two_step_chord h4 G hBase f i d hi)

end CCO.TypedOrbitFrames
