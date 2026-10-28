import CCO.RawExact.WalkCertificateTransport
import CCO.RawExact.CertifiedTraceToWord
import CCO.RawExact.WalkColourIndependence

/-!
# B002 C13: colour-preserving replacement of all points in a RAW walk

Start from ONE genuine old `WordPath` for a typed equality-inclusive
RAW word. Another finite list of ACTUAL tagged original-sort points
with the same word sort trace and exactly the same full old typed
pair colours on corresponding diversity edges itself realizes the
very SAME RAW word, with precisely its displayed endpoints.

There is no injectivity or old source homogeneity premise for this
lemma, and the new word's endpoint relation may be the logical
diagonal even when it has positive diversity length. This is the
independent bridge from a completed source-coloured fan to
the exact-ball relational statement.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- Genuine equality-inclusive RAW word realizability is invariant
under replacing the complete real trace by another old point trace
with the same original sort sequence and per-edge atomic colours. -/
theorem wordPath_of_same_real_trace_colours
    {i j : ι} (word : RawWord S i j)
    {x : X i} {y : X j}
    (path : WordPath S word x y)
    (newPoints : List (Sigma X))
    (hSort : newPoints.map Sigma.fst = wordSortTrace S word)
    (hSame : SameEdgeColours S (realWalkTrace S path) newPoints) :
    ∃ (x' : X i) (y' : X j)
      (newPath : WordPath S word x' y'),
      realWalkTrace S newPath = newPoints := by
  have hOldCert :=
    realWalkTrace_certified S path
  have hOldSort :=
    realWalkTrace_sorts S path
  have hNewCert :=
    typedWalkCertificate_of_same_colours S
      hOldCert hSame (hOldSort.trans hSort.symm)
  exact wordPath_of_certified_sort_trace S word newPoints hNewCert hSort

end CCO.RawExact
