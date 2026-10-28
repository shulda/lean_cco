import CCO.RawExact.FanTerminalIncidence
import CCO.RawExact.FanInteriorIsolation
import CCO.RawExact.PathEndpointEdges
import Mathlib.Tactic

/-!
# B002 C12: overlaps between distinct private RAW word occurrences

Private paths have disjoint formal interiors. Two separate word
occurrences may share only the root or the very same actual tagged
old centre. In particular, when two path edges coincide as ordered
pairs of formal vertices, they either belong to ONE occurrence or
they are both one-diversity-letter direct spokes. This is the exact
incidence separation needed for the later unique atomic labelling.

Identity letters introduce no edges; there is no assumption of
injectivity of actual old word walks, SAP, CCO or full ball Helly.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {root : ι} {I : Type (max u v)} [Finite I]
variable {sort : I → ι}

/-- Sharing even ONE formal private interior forces the same original
word occurrence (including its menu index and actual list slot). -/
theorem privateFan_shared_interior_same_occurrence
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (o o' : WordOccurrence S D)
    (p : PathPosition S (occurrenceWord S D o))
    (q : PathPosition S (occurrenceWord S D o'))
    (hp0 : p.val ≠ 0)
    (hpEnd : p.val ≠ diversityLength S (occurrenceWord S D o))
    (hShared : privateFanAtWordPosition S D centres o p =
      privateFanAtWordPosition S D centres o' q) :
    o = o' := by
  have hp := privateFanAt_interior S D centres o p hp0 hpEnd
  have ho' := privateFanAt_interior_occurrence S D centres
    o ⟨p, hp0, hpEnd⟩ o' q (hShared.symm.trans hp)
  exact ho'.symm

/-- If two DIFFERENT word occurrences share a formal path vertex,
then that vertex must be an endpoint in BOTH words. No private
interior can be glued across occurrences. -/
theorem privateFan_different_occurrences_share_only_endpoints
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (o o' : WordOccurrence S D)
    (hDifferent : o ≠ o')
    (p : PathPosition S (occurrenceWord S D o))
    (q : PathPosition S (occurrenceWord S D o'))
    (hShared : privateFanAtWordPosition S D centres o p =
      privateFanAtWordPosition S D centres o' q) :
    (p.val = 0 ∨ p.val = diversityLength S (occurrenceWord S D o)) ∧
    (q.val = 0 ∨ q.val = diversityLength S (occurrenceWord S D o')) := by
  constructor
  · by_cases hp0 : p.val = 0
    · exact Or.inl hp0
    · by_cases hpEnd : p.val = diversityLength S (occurrenceWord S D o)
      · exact Or.inr hpEnd
      · exact False.elim (hDifferent
          (privateFan_shared_interior_same_occurrence S D centres
            o o' p q hp0 hpEnd hShared))
  · by_cases hq0 : q.val = 0
    · exact Or.inl hq0
    · by_cases hqEnd : q.val = diversityLength S (occurrenceWord S D o')
      · exact Or.inr hqEnd
      · exact False.elim (hDifferent.symm
          (privateFan_shared_interior_same_occurrence S D centres
            o' o q p hq0 hqEnd hShared.symm))

/-- Convert the numeric endpoint alternatives into equality
with the actual first or last finite path position. -/
theorem pathPosition_endpoint_of_value {i j : ι}
    (word : RawWord S i j)
    (p : PathPosition S word)
    (hp : p.val = 0 ∨ p.val = diversityLength S word) :
    p = pathStart S word ∨ p = pathFinish S word := by
  rcases hp with hp0 | hpEnd
  · exact Or.inl (Fin.ext hp0)
  · exact Or.inr (Fin.ext hpEnd)

/-- The collision theorem for private path EDGES. If two edges
between the same ordered pair of formal fan vertices are attributed
to different word occurrences, BOTH words contain exactly one
genuine diversity edge. All remaining path edges are occurrence-private.
This theorem is purely combinatorial; comparing the two direct atoms
uses the separately proved pairwise-ball theorem. -/
theorem privateFan_overlapping_path_edges_same_or_direct
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (o o' : WordOccurrence S D)
    (p q : PathPosition S (occurrenceWord S D o))
    (p' q' : PathPosition S (occurrenceWord S D o'))
    (hpq : pathAdjacent S (occurrenceWord S D o) p q)
    (hpq' : pathAdjacent S (occurrenceWord S D o') p' q')
    (hStart : privateFanAtWordPosition S D centres o p =
      privateFanAtWordPosition S D centres o' p')
    (hFinish : privateFanAtWordPosition S D centres o q =
      privateFanAtWordPosition S D centres o' q') :
    o = o' ∨
      (diversityLength S (occurrenceWord S D o) = 1 ∧
       diversityLength S (occurrenceWord S D o') = 1) := by
  by_cases hSame : o = o'
  · exact Or.inl hSame
  · have hP := privateFan_different_occurrences_share_only_endpoints
      S D centres o o' hSame p p' hStart
    have hQ := privateFan_different_occurrences_share_only_endpoints
      S D centres o o' hSame q q' hFinish
    have hp := pathPosition_endpoint_of_value S
      (occurrenceWord S D o) p hP.1
    have hq := pathPosition_endpoint_of_value S
      (occurrenceWord S D o) q hQ.1
    have hp' := pathPosition_endpoint_of_value S
      (occurrenceWord S D o') p' hP.2
    have hq' := pathPosition_endpoint_of_value S
      (occurrenceWord S D o') q' hQ.2
    exact Or.inr ⟨
      pathAdjacent_endpoint_edge_is_single_atom S
        (occurrenceWord S D o) p q hp hq hpq,
      pathAdjacent_endpoint_edge_is_single_atom S
        (occurrenceWord S D o') p' q' hp' hq' hpq'⟩

end CCO.RawExact
