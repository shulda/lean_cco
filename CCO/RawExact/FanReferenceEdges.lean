import CCO.RawExact.FanSortCompatibility
import CCO.RawExact.ActualWordStepColour
import Mathlib.Tactic

/-!
# B002 C12: every formal private word edge has a genuine old source colour

The graph of private RAW word occurrences is formal. Its edge labels
must nevertheless come from REAL original atomic relations, rather
than from a fabricated colour table. Each occurrence has an
independently chosen actual reference walk, and each consecutive
pair in that walk has a true diversity atom. Reversing an edge uses
the named typed converse. Together with FanSortCompatibility this
supplies exactly the actual atomic data for future C12 edge labelling.

There is no global joint real realization of the fan assumed here;
such a realization is the conclusion of the Helly argument.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- A genuine old diversity edge can be used in the opposite
direction, with the actual typed converse atom. -/
theorem genuineEdge_reverse
    (p q : Sigma X) (h : GenuineEdge S p q) :
    GenuineEdge S q p := by
  rcases p with ⟨i, x⟩
  rcases q with ⟨j, y⟩
  obtain ⟨a, ha⟩ := h
  exact ⟨S.conv a, (S.colour_swap x y a).mp ha⟩

/-- A single forward formal step of a given word occurrence is
realized by a genuinely old coloured diversity edge in its
independent reference walk, with matching finite indices. -/
theorem referencePointAt_genuine_forward
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    {root : ι} {I : Type (max u v)} [Finite I]
    {sort : I → ι}
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (o : WordOccurrence S D)
    (p q : PathPosition S (occurrenceWord S D o))
    (hStep : p.val + 1 = q.val) :
    GenuineEdge S
      (referencePointAt S H D centres o p)
      (referencePointAt S H D centres o q) := by
  let path := (referenceOccurrenceWalk S H D centres o).2
  have hLength : (realWalkTrace S path).length =
      diversityLength S (occurrenceWord S D o) + 1 :=
    realWalkTrace_length S path
  have hpBound : p.val + 1 < (realWalkTrace S path).length := by
    rw [hLength]
    have hqBound := q.isLt
    omega
  have hReal := (List.isChain_iff_getElem.mp
    (realWordPath_isChain S path)) p.val hpBound
  have hqVal : q.val = p.val + 1 := hStep.symm
  simpa only [referencePointAt, List.get_eq_getElem, hqVal] using hReal

/-- EVERY actual private-word edge, in either orientation, has
the corresponding genuine ORIGINAL diversity atom from its
reference word witness. It does not require the reference root
to coincide with any other occurrence's reference root. -/
theorem referencePointAt_genuine_adjacent
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    {root : ι} {I : Type (max u v)} [Finite I]
    {sort : I → ι}
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (o : WordOccurrence S D)
    (p q : PathPosition S (occurrenceWord S D o))
    (hAdj : pathAdjacent S (occurrenceWord S D o) p q) :
    GenuineEdge S
      (referencePointAt S H D centres o p)
      (referencePointAt S H D centres o q) := by
  rcases (pathAdjacent_iff_step S (occurrenceWord S D o) p q).mp hAdj with
    hForward | hBackward
  · exact referencePointAt_genuine_forward S H D centres o p q hForward
  · exact genuineEdge_reverse S _ _
      (referencePointAt_genuine_forward S H D centres o q p hBackward)

/-- Adjacent formal private vertices have actual reference points
with matching original sorts AND a genuine original diversity atom.
This formulation avoids making a synthetically typed fan palette. -/
theorem privateFan_path_edge_real_colour
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    {root : ι} {I : Type (max u v)} [Finite I]
    {sort : I → ι}
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (o : WordOccurrence S D)
    (p q : PathPosition S (occurrenceWord S D o))
    (hAdj : pathAdjacent S (occurrenceWord S D o) p q) :
    privateFanSort S D centres
        (privateFanAtWordPosition S D centres o p) =
          (referencePointAt S H D centres o p).1 ∧
      privateFanSort S D centres
        (privateFanAtWordPosition S D centres o q) =
          (referencePointAt S H D centres o q).1 ∧
      GenuineEdge S
        (referencePointAt S H D centres o p)
        (referencePointAt S H D centres o q) := by
  exact ⟨privateFan_referencePoint_sort S H D centres o p,
    privateFan_referencePoint_sort S H D centres o q,
    referencePointAt_genuine_adjacent S H D centres o p q hAdj⟩

end CCO.RawExact
