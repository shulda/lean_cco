import CCO.RawExact.WalkColourIndependence
import CCO.RawExact.OccurrenceRealizations
import CCO.RawExact.WordOccurrences

/-!
# B002 C12: transfer of actual private-path edge colours to pair witnesses

A reference walk is selected for EACH original RAW word occurrence
merely to label the finite private fan. On a simple cycle involving
two private paths, the source proof uses a DIFFERENT pairwise-common-root
witness for those two words. These pairwise witnesses must realize
exactly the reference edge colours: this is now a proven fact,
not an assumption that choices of old real walks are coherent.

The two occurrences may belong to one exact menu, to different menus
with the SAME actual old centre, or to different old centre sorts.
There is no SAP or quotient action hypothesis.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- Two independently selected reference paths can both be replaced
by genuine walks with ONE common old root, each preserving all
of its own original RAW edge colours. -/
theorem paired_private_walks_match_reference_colours
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    {root : ι} {I : Type (max u v)} [Finite I]
    {sort : I → ι}
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (hPair : ∀ p q : I,
      (ball (evaluate S (D p).words) (centres p) ∩
        ball (evaluate S (D q).words) (centres q)).Nonempty)
    (p q : WordOccurrence S D) :
    Nonempty (Σ x : X root,
      Σ wp : WordPath S (occurrenceWord S D p) x (centres p.1),
      Σ wq : WordPath S (occurrenceWord S D q) x (centres q.1),
        SameEdgeColours S
          (realWalkTrace S (referenceOccurrenceWalk S H D centres p).2)
          (realWalkTrace S wp) ∧
        SameEdgeColours S
          (realWalkTrace S (referenceOccurrenceWalk S H D centres q).2)
          (realWalkTrace S wq)) := by
  obtain ⟨⟨x, wp, wq⟩⟩ :=
    pair_private_walks_of_pairwise_balls S D centres hPair p q
  refine ⟨⟨x, wp, wq, ?_, ?_⟩⟩
  · exact sameEdgeColours_of_wordPaths S (occurrenceWord S D p)
      (referenceOccurrenceWalk S H D centres p).2 wp
  · exact sameEdgeColours_of_wordPaths S (occurrenceWord S D q)
      (referenceOccurrenceWalk S H D centres q).2 wq

end CCO.RawExact
