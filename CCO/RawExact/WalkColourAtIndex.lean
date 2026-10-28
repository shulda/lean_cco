import CCO.RawExact.WalkColourIndependence
import Mathlib.Tactic

/-!
# B002 C12: pointwise original atomic-colour invariance of RAW word walks

The already-proved `SameEdgeColours` theorem compares two complete
independently realized RAW paths. A finite private-fan labelling,
however, needs the equality at EACH numbered diversity edge.

These lemmas extract that precise index equality, including arbitrary
typed intermediate sorts, identity letters, and noninjective old
walk witnesses. They use only actual atomic certificates; not CCO,
SAP or exact-ball Helly.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- The recursive `SameEdgeColours` condition makes the source's
true typed pair colour equal at EVERY corresponding consecutive
finite index, not merely at the first edge. -/
theorem sameEdgeColours_getElem
    (pts pts' : List (Sigma X))
    (h : SameEdgeColours S pts pts')
    (k : Nat)
    (hk : k + 1 < pts.length)
    (hk' : k + 1 < pts'.length) :
    taggedColour S
      (pts[k]'(by omega)) (pts[k + 1]'hk) =
    taggedColour S
      (pts'[k]'(by omega)) (pts'[k + 1]'hk') := by
  induction k generalizing pts pts' with
  | zero =>
      cases pts with
      | nil => simp at hk
      | cons p xs =>
        cases xs with
        | nil => simp at hk
        | cons q tail =>
          cases pts' with
          | nil => simp at hk'
          | cons p' xs' =>
            cases xs' with
            | nil => simp at hk'
            | cons q' tail' =>
              simpa only [List.getElem_cons_zero,
                List.getElem_cons_succ] using h.1
  | succ k ih =>
      cases pts with
      | nil => simp at hk
      | cons p xs =>
        cases xs with
        | nil => simp at hk
        | cons q tail =>
          cases pts' with
          | nil => simp at hk'
          | cons p' xs' =>
            cases xs' with
            | nil => simp at hk'
            | cons q' tail' =>
              have hTail : SameEdgeColours S
                  (q :: tail) (q' :: tail') := h.2
              have hkTail : k + 1 < (q :: tail).length := by
                simp only [List.length_cons] at hk ⊢
                omega
              have hkTail' : k + 1 < (q' :: tail').length := by
                simp only [List.length_cons] at hk' ⊢
                omega
              have hAt :=
                ih (q :: tail) (q' :: tail') hTail hkTail hkTail'
              simpa only [List.getElem_cons_succ] using hAt

/-- Any two actual RAW word-path realizations carry the same full
dependent original edge colour at every consecutive diversity
position. Reference roots and internal point values may differ. -/
theorem wordPaths_tagged_edge_colour_eq
    {i j : ι}
    (word : RawWord S i j)
    {x x' : X i} {y y' : X j}
    (path : WordPath S word x y)
    (path' : WordPath S word x' y')
    (k : Fin (diversityLength S word)) :
    taggedColour S
      ((realWalkTrace S path)[k.val]'(by
        rw [realWalkTrace_length S path]
        omega))
      ((realWalkTrace S path)[k.val + 1]'(by
        rw [realWalkTrace_length S path]
        omega)) =
    taggedColour S
      ((realWalkTrace S path')[k.val]'(by
        rw [realWalkTrace_length S path']
        omega))
      ((realWalkTrace S path')[k.val + 1]'(by
        rw [realWalkTrace_length S path']
        omega)) := by
  have hk : k.val + 1 < (realWalkTrace S path).length := by
    rw [realWalkTrace_length S path]
    omega
  have hk' : k.val + 1 < (realWalkTrace S path').length := by
    rw [realWalkTrace_length S path']
    omega
  exact sameEdgeColours_getElem S
    (realWalkTrace S path)
    (realWalkTrace S path')
    (sameEdgeColours_of_wordPaths S word path path')
    k.val hk hk'

end CCO.RawExact
