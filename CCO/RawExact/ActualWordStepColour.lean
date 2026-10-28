import CCO.RawExact.CertifiedWalkChain
import Mathlib.Data.List.Chain

/-!
# B002 C12: every actual private RAW word edge has a genuine old atom

A realized RAW word of diversity length n produces exactly n+1 tagged
old points and a chain of n genuine original atomic edges. At every
consecutive pair of positions there is a true typed diversity atom.
This is the source-level existence theorem required before assigning
real atomic colours to every edge in the full private fan graph.

Identity letters produce no edges. Positive words may still have
logical identity as an OUTPUT; no injectivity is assumed.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- A genuine source atomic colour at every consecutive position of
any actual represented RAW WordPath. The typing comes from the two
actual tagged original-sort points; no abstract colour table exists. -/
theorem realWordPath_edge_is_genuine
    {i j : ι} {word : RawWord S i j}
    {x : X i} {y : X j}
    (path : WordPath S word x y)
    (k : Fin (diversityLength S word)) :
    GenuineEdge S
      ((realWalkTrace S path)[k.val]'(by
        rw [realWalkTrace_length S path]
        omega))
      ((realWalkTrace S path)[k.val + 1]'(by
        rw [realWalkTrace_length S path]
        omega)) := by
  have hLength : (realWalkTrace S path).length =
      diversityLength S word + 1 :=
    realWalkTrace_length S path
  have hk : k.val + 1 < (realWalkTrace S path).length := by
    rw [hLength]
    omega
  exact (List.isChain_iff_getElem.mp (realWordPath_isChain S path))
    k.val hk

end CCO.RawExact
