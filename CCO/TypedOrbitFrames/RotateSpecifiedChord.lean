import CCO.TypedOrbitFrames.RotateOldSideReading
import CCO.TypedOrbitFrames.ChordShortRight

/-!
# B053 C04: normalize an arbitrary TRUE typed old source chord

A proper nonconsecutive old cyclic chord s--t on an actual
SimpleCycle D can be translated to the genuine 0--k chord
with k=(t-s).val. The OLD typed source edge certificate on
t→s is transported to the rotated SimpleCycle, including
the dependent original sort and old diversity atom.

No new diversity identity, inferred old completion, hidden SAP,
or quotient-homogeneity instance is introduced.
-/

namespace CCO.TypedOrbitFrames

open CCO.ParityHasse.Sparse

universe u v w z
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {V : Type z}

/-- A chord is specified by an ACTUAL original typed diversity
atom from t to s. In particular this hypothesis is stronger
than an uncoloured graph edge, and it never treats equality
as a positive atom. -/
def OriginalArbitrarySpecifiedChord
    {D : PartialDiagram S V} (C : SimpleCycle D)
    [NeZero C.length] (s t : ZMod C.length) : Prop :=
  ∃ hne :
      C.vertices (zmodFinCode C.length t) ≠
        C.vertices (zmodFinCode C.length s),
    ∃ a : S.Atom
        (D.vertexSort (C.vertices (zmodFinCode C.length t)))
        (D.vertexSort (C.vertices (zmodFinCode C.length s))),
      D.edge (C.vertices (zmodFinCode C.length t))
        (C.vertices (zmodFinCode C.length s)) hne = some a

/-- ANY actual original diversity chord t→s can be normalized,
including the wrap-around case, using ONE cyclic source rotation.
The SAME old atom and the SAME proof-indexed source D.edge
are preserved on the rotated 0--k chord. -/
theorem original_arbitrary_specified_chord_rotates
    {D : PartialDiagram S V} (C : SimpleCycle D)
    [NeZero C.length] (hn : 4 ≤ C.length)
    (s t : ZMod C.length)
    (hProper : OriginalZModProperChord s t)
    (hEdge : OriginalArbitrarySpecifiedChord S C s t) :
    OriginalNormalizedSpecifiedChord S
      (originalRotateOldSimpleCycle S C s)
      (original_zmod_proper_chord_has_cut hn s t hProper) := by
  let cut : OriginalChordCut C.length (t-s).val :=
    original_zmod_proper_chord_has_cut hn s t hProper
  obtain ⟨hne,a,ha⟩ := hEdge
  have hK :
      (originalRotateOldSimpleCycle S C s).vertices
          (originalChordOldK cut) =
        C.vertices (zmodFinCode C.length t) := by
    change C.vertices
      (originalCycleRotateIndex s (originalChordOldK cut)) =
      C.vertices (zmodFinCode C.length t)
    apply congrArg C.vertices
    simpa only [originalChordOldK] using
      (original_cycle_rotate_chord_other s t)
  have h0 :
      (originalRotateOldSimpleCycle S C s).vertices
          (originalChordOldZero cut) =
        C.vertices (zmodFinCode C.length s) := by
    change C.vertices
      (originalCycleRotateIndex s (originalChordOldZero cut)) =
      C.vertices (zmodFinCode C.length s)
    apply congrArg C.vertices
    simpa only [originalChordOldZero] using
      (original_cycle_rotate_zero C.length_pos s)
  change OriginalNormalizedSpecifiedChord S
    (originalRotateOldSimpleCycle S C s) cut
  exact original_old_specified_edge_witness_congr S
    hK.symm h0.symm hne
    ((originalRotateOldSimpleCycle S C s).vertices.injective.ne
      (original_chord_old_K_ne_zero cut))
    ⟨a,ha⟩

end CCO.TypedOrbitFrames
