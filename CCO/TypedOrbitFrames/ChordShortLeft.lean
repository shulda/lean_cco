import CCO.TypedOrbitFrames.ChordArcSuccessor
import CCO.TypedOrbitFrames.OldPartialPullback

/-!
# B053 C04: the actual SHORT left typed cycle of a specified OLD chord

A true source SimpleCycle D is an injective cyclic list of typed
old formal vertices with actual diversity atoms on EVERY side.
A normalized proper chord 0--k is a separately specified
OLD diversity edge from position k to position 0.

This module constructs an actual strict shorter `SimpleCycle D`
on positions 0,1,...,k, closed by that SAME old chord k→0.
All internal sides are literally inherited from the original
SimpleCycle, not invented independent atomic edge colours.
Its vertices form a genuine embedding of Fin(k+1) into the
original source vertex type; it therefore uses no old-age
SAP or CCO completion hypothesis.

The right short cycle is the next distinct source obligation.
-/

universe u v w z
namespace CCO.TypedOrbitFrames

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {V : Type z}

/-- Actual k endpoint of a normalized proper chord in an n-cycle. -/
def originalChordOldK {n k : Nat} (cut : OriginalChordCut n k) : Fin n :=
  ⟨k, by have h:=cut.right_nontrivial; omega⟩

/-- Actual zero endpoint of a normalized proper chord in an n-cycle. -/
def originalChordOldZero {n k : Nat} (cut : OriginalChordCut n k) : Fin n :=
  ⟨0, by have h:=cut.right_nontrivial; omega⟩

/-- A genuine proper chord cannot be an OLD positive identity. -/
theorem original_chord_old_K_ne_zero {n k : Nat}
    (cut : OriginalChordCut n k) :
    originalChordOldK cut ≠ originalChordOldZero cut := by
  intro h
  have hv := congrArg Fin.val h
  have hc := cut.left_nontrivial
  change k = 0 at hv
  omega

/-- Real true source chord, with its EXACT old typed diversity atom
and the literal old partial-diagram edge proof. Neither a
new positive identity nor an arbitrary graph chord qualifies. -/
def OriginalNormalizedSpecifiedChord
    {D : PartialDiagram S V} (C : SimpleCycle D)
    {k : Nat} (cut : OriginalChordCut C.length k) : Prop :=
  ∃ a : S.Atom
      (D.vertexSort (C.vertices (originalChordOldK cut)))
      (D.vertexSort (C.vertices (originalChordOldZero cut))),
    D.edge (C.vertices (originalChordOldK cut))
        (C.vertices (originalChordOldZero cut))
        (C.vertices.injective.ne (original_chord_old_K_ne_zero cut)) =
          some a

/-- Genuine SHORT left subcycle index embedding, preserving literal
old source typed vertex names, without collapsing formal positions. -/
def originalChordLeftSourceEmbedding
    {D : PartialDiagram S V} (C : SimpleCycle D)
    {k : Nat} (cut : OriginalChordCut C.length k) :
    Fin (k + 1) ↪ V :=
  (⟨originalChordLeftIndex cut,
    original_chord_left_injective cut⟩ :
      Fin (k + 1) ↪ Fin C.length).trans C.vertices

/-- A cyclic successor of a finite ordinal with at least three
vertices is never its own vertex. This is the genuine old
diversity-side nonidentity guard for all shorter cycles. -/
theorem original_short_cycle_next_ne
    {m : Nat} (hm : 3 ≤ m)
    (p : Fin m) :
    p ≠ CCO.cyclicNext (by omega : 0 < m) p := by
  intro h
  have hv := congrArg Fin.val h
  have hp := p.isLt
  change p.val = (p.val + 1) % m at hv
  by_cases hn : p.val + 1 < m
  · rw [Nat.mod_eq_of_lt hn] at hv
    omega
  · have he : p.val + 1 = m := by omega
    rw [he, Nat.mod_self] at hv
    omega

/-- Source11 C04 proper left STRICT shorter cycle in the SAME
original PartialDiagram D. Its consecutive old sides are
exactly the original ones, and its closing edge is the given
real specified old chord. This is actual typed `SimpleCycle`,
not merely an abstract graph path and not its `CycleHom`. -/
def originalChordLeftShortCycle
    {D : PartialDiagram S V} (C : SimpleCycle D)
    {k : Nat} (cut : OriginalChordCut C.length k)
    (hChord : OriginalNormalizedSpecifiedChord S C cut) :
    SimpleCycle D := by
  let e := originalChordLeftSourceEmbedding S C cut
  have hm : 3 ≤ k + 1 := by
    have hc := cut.left_nontrivial
    omega
  refine {
    length := k + 1
    length_ge_three := hm
    length_pos := by omega
    vertices := e
    next_ne := ?_
    specified := ?_
  }
  · intro p
    exact e.injective.ne (original_short_cycle_next_ne hm p)
  · intro p
    by_cases hp : p.val < k
    · have hindex := original_chord_left_internal_next cut p hp
      change ∃ a, D.edge
        (C.vertices (originalChordLeftIndex cut p))
        (C.vertices (originalChordLeftIndex cut
          (CCO.cyclicNext (by omega : 0 < k + 1) p))) _ =
            some a
      simpa only [← hindex] using
        (C.specified (originalChordLeftIndex cut p))
    · have hval := p.isLt
      have hpK : p = (⟨k, by omega⟩ : Fin (k + 1)) := by
        apply Fin.ext
        change p.val = k
        omega
      rw [hpK]
      change ∃ a, D.edge
        (C.vertices (originalChordLeftIndex cut
          (⟨k, by omega⟩ : Fin (k + 1))))
        (C.vertices (originalChordLeftIndex cut
          (CCO.cyclicNext (by omega : 0 < k + 1)
            (⟨k, by omega⟩ : Fin (k + 1))))) _ =
          some a
      simpa [OriginalNormalizedSpecifiedChord,
        originalChordOldK, originalChordOldZero,
        originalChordLeftIndex, CCO.cyclicNext] using hChord

end CCO.TypedOrbitFrames
