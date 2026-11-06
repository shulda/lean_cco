import CCO.TypedOrbitFrames.CycleHomReadingConverse
import CCO.TypedOrbitFrames.ChordCycleStep

/-!
# B053 C04: a genuinely typed old SimpleCycle from two shorter arc readings

The already compiled old-source `original_normalized_chord_old_sap_cycle_step`
produces an actual old finite induced target and one Sigma-valued
tuple preserving every side of a long cycle from two shorter
old-coloured arc realizations, using ONLY original homogeneous
source and OLD AgeSAP on finite induced IMAGES.

Here its output is converted into an actual `CCO.CycleHom C` of
the original old typed `SimpleCycle`, not just an untyped graph
homomorphism. The two SHORTER side readings are explicit hypotheses
meant to be furnished by the genuine structural induction;
the long `CycleHom C` is strictly the conclusion, never an input.

This theorem is the normalized-one-chord induction STEP. Still open:
construction of the literal shorter `CCO.SimpleCycle` diagrams
from an arbitrary old cycle and its specified chord, propagation
of their actual source `CycleHom` under recursion, and normalizing
every possible-position chord by cyclic rotation before induction.
-/

universe u v w t z
namespace CCO.TypedOrbitFrames

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]
variable {V : Type z}

/-- The actual typed `CycleHom` of a SOURCE old simple cycle,
from complete left/right old-colour readings on the strictly
shorter arcs and their common genuinely coloured chord.

No automorphism-group equality for hidden structures, no hidden
SAP, no invented equality atom, and no hypothesis of long-cycle
realizability. The displayed named original sorts and all actual
original atomic colours are retained in the conclusion. -/
theorem original_normalized_chord_typed_cycle_hom
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {D : PartialDiagram S V} (C : SimpleCycle D)
    {k : Nat} (cut : OriginalChordCut C.length k)
    (left : Fin (k + 1) → Sigma X)
    (right : Fin (C.length - k + 1) → Sigma X)
    {i j : ι} (a : S.Atom i j)
    (x x' : X i) (y y' : X j)
    (hxy : S.colour x y = some a)
    (hx'y' : S.colour x' y' = some a)
    (hLeftK : left ⟨k, by have := cut.right_nontrivial; omega⟩ =
      (⟨i,x⟩ : Sigma X))
    (hLeft0 : left ⟨0, by have := cut.right_nontrivial; omega⟩ =
      (⟨j,y⟩ : Sigma X))
    (hRightK : right ⟨0, by have := cut.right_nontrivial; omega⟩ =
      (⟨i,x'⟩ : Sigma X))
    (hRight0 : right ⟨C.length - k, by
      have := cut.right_nontrivial; omega⟩ =
      (⟨j,y'⟩ : Sigma X))
    (hLeftSide : ∀ a b : Fin (k + 1), a.val + 1 = b.val →
      taggedColour S (left a) (left b) =
        originalSpecifiedCycleSideReading S C
          (originalChordLeftIndex cut a))
    (hRightSide : ∀ a b : Fin (C.length - k + 1),
      a.val + 1 = b.val →
      taggedColour S (right a) (right b) =
        originalSpecifiedCycleSideReading S C
          (originalChordRightIndex cut a)) :
    CycleHom C := by
  obtain ⟨M,whole,hmem,hread⟩ :=
    original_normalized_chord_old_sap_cycle_step
      S H sap cut left right
      (originalSpecifiedCycleSideReading S C)
      a x x' y y' hxy hx'y'
      hLeftK hLeft0 hRightK hRight0
      hLeftSide hRightSide
  exact original_coloured_side_reading_is_cycle_hom
    S C whole (by intro p; exact hread p)

end CCO.TypedOrbitFrames
