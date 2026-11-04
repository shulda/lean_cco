import CCO.TypedOrbitFrames.ChordShortLeft

/-!
# B053 C04: the actual SHORT right typed cycle of a specified old chord

The second strict short cycle is the original directed arc
k→k+1→...→n-1→0, then the SAME genuine specified old
chord in the converse orientation 0→k. Its original
typed atoms, including the old n-1→0 side, are used
literally; the closing edge comes from the actual
D.edge_reverse theorem rather than a fabricated atom.

Together with ChordShortLeft this constructs both
actual shorter `CCO.SimpleCycle D` objects needed by
the source11 well-founded chord induction. They still
require the separately formalized recursive CycleHom
proof and input chord extraction at arbitrary positions.
-/

universe u v w z
namespace CCO.TypedOrbitFrames

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {V : Type z}

/-- Genuine RIGHT source short-cycle injection into the old
partial diagram, with last short vertex mapping to old index 0. -/
def originalChordRightSourceEmbedding
    {D : PartialDiagram S V} (C : SimpleCycle D)
    {k : Nat} (cut : OriginalChordCut C.length k) :
    Fin (C.length - k + 1) ↪ V :=
  (⟨originalChordRightIndex cut,
    original_chord_right_injective cut⟩ :
      Fin (C.length - k + 1) ↪ Fin C.length).trans C.vertices

/-- Source11 C04 actual right strict shorter old typed
SimpleCycle, with every real old directed side inherited,
including the wrap n-1→0, and the converse old chord 0→k.
No AgeSAP is invoked during the construction of this
formal SHORT cycle: SAP is used only later to glue the
actual homomorphic image objects of its realizations. -/
def originalChordRightShortCycle
    {D : PartialDiagram S V} (C : SimpleCycle D)
    {k : Nat} (cut : OriginalChordCut C.length k)
    (hChord : OriginalNormalizedSpecifiedChord S C cut) :
    SimpleCycle D := by
  let e := originalChordRightSourceEmbedding S C cut
  have hm : 3 ≤ C.length - k + 1 := by
    have hc := cut.right_nontrivial
    omega
  refine {
    length := C.length - k + 1
    length_ge_three := hm
    length_pos := by omega
    vertices := e
    next_ne := ?_
    specified := ?_
  }
  · intro p
    exact e.injective.ne (original_short_cycle_next_ne hm p)
  · intro p
    by_cases hp : p.val < C.length - k
    · have hindex := original_chord_right_internal_next cut p hp
      change ∃ a, D.edge
        (C.vertices (originalChordRightIndex cut p))
        (C.vertices (originalChordRightIndex cut
          (CCO.cyclicNext
            (by have hc := cut.right_nontrivial; omega :
              0 < C.length - k + 1) p))) _ = some a
      simpa only [hindex] using
        (C.specified (originalChordRightIndex cut p))
    · have hval := p.isLt
      have hpLast :
          p = (⟨C.length - k, by omega⟩ :
            Fin (C.length - k + 1)) := by
        apply Fin.ext
        change p.val = C.length - k
        omega
      rw [hpLast]
      change ∃ a, D.edge
        (C.vertices (originalChordRightIndex cut
          (⟨C.length - k, by omega⟩ :
            Fin (C.length - k + 1))))
        (C.vertices (originalChordRightIndex cut
          (CCO.cyclicNext
            (by have hc := cut.right_nontrivial; omega :
              0 < C.length - k + 1)
            (⟨C.length - k, by omega⟩ :
              Fin (C.length - k + 1))))) _ = some a
      obtain ⟨a,ha⟩ := hChord
      have hreverse : D.edge
          (C.vertices (originalChordOldZero cut))
          (C.vertices (originalChordOldK cut))
          (C.vertices.injective.ne
            (original_chord_old_K_ne_zero cut)).symm =
            some (S.conv a) :=
        (D.edge_reverse
          (C.vertices (originalChordOldK cut))
          (C.vertices (originalChordOldZero cut))
          (C.vertices.injective.ne
            (original_chord_old_K_ne_zero cut)) a).mp ha
      simpa only [original_chord_right_last cut,
        original_chord_right_closing_next cut] using
        (show ∃ c, D.edge
          (C.vertices (originalChordOldZero cut))
          (C.vertices (originalChordOldK cut)) _ = some c
          from ⟨S.conv a,hreverse⟩)

end CCO.TypedOrbitFrames
