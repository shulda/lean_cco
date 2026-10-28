import CCO.RawExact.FanEdgeOverlaps
import Mathlib.Tactic

/-!
# B002 C12: two coincident direct spokes attach to the same actual old centre

If two distinct private RAW word occurrences share a formal edge,
their paths are both one-diversity-step paths. The two shared formal
endpoints then force both paths to end at precisely the SAME tagged
original real centre. This is stronger than mere sameness of centre
sorts, and is the exact overlap required when applying the previously
proved duplicate-direct-edge atomic-colour theorem.

All assertions are unconditional finite path combinatorics; there
is no assumed CCO, SAP or source-level exact-ball Helly theorem.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {root : ι} {I : Type (max u v)} [Finite I]
variable {sort : I → ι}

/-- Every edge in a one-diversity-letter path has an initial
endpoint. The opposite endpoint is necessarily the last position. -/
theorem unit_path_edge_has_start {i j : ι}
    (word : RawWord S i j)
    (hLength : diversityLength S word = 1)
    (p q : PathPosition S word)
    (hAdj : pathAdjacent S word p q) :
    p = pathStart S word ∨ q = pathStart S word := by
  have hpBound : p.val < 2 := by
    have hp := p.isLt
    omega
  have hqBound : q.val < 2 := by
    have hq := q.isLt
    omega
  change p.val + 1 = q.val ∨ q.val + 1 = p.val at hAdj
  rcases hAdj with hForward | hBackward
  · left
    apply Fin.ext
    change p.val = 0
    omega
  · right
    apply Fin.ext
    change q.val = 0
    omega

theorem unit_path_edge_other_is_finish {i j : ι}
    (word : RawWord S i j)
    (hLength : diversityLength S word = 1)
    (p q : PathPosition S word)
    (hAdj : pathAdjacent S word p q)
    (hp : p = pathStart S word) :
    q = pathFinish S word := by
  subst p
  have hq := (pathAdjacent_start_iff S word q).mp hAdj
  apply Fin.ext
  change q.val = diversityLength S word
  omega

/-- Coincident formal finishing vertices of two positive RAW
occurrences correspond to the very same ACTUAL centre value,
not merely two centres with equal original sort. -/
theorem privateFan_shared_finishes_same_centre
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (o o' : WordOccurrence S D)
    (p : PathPosition S (occurrenceWord S D o))
    (q : PathPosition S (occurrenceWord S D o'))
    (hp : p = pathFinish S (occurrenceWord S D o))
    (hq : q = pathFinish S (occurrenceWord S D o'))
    (hLength : 0 < diversityLength S (occurrenceWord S D o))
    (hLength' : 0 < diversityLength S (occurrenceWord S D o'))
    (hShared : privateFanAtWordPosition S D centres o p =
      privateFanAtWordPosition S D centres o' q) :
    toDistinctCentre sort centres o.1 =
      toDistinctCentre sort centres o'.1 := by
  have hLeft : privateFanAtWordPosition S D centres o p =
      privateFanCentre S D centres (toDistinctCentre sort centres o.1) := by
    rw [hp]
    exact privateFanAt_finish S D centres o hLength
  have hRight : privateFanAtWordPosition S D centres o' q =
      privateFanCentre S D centres (toDistinctCentre sort centres o'.1) := by
    rw [hq]
    exact privateFanAt_finish S D centres o' hLength'
  exact privateFanCentre_injective S D centres
    (hLeft.symm.trans (hShared.trans hRight))

/-- Two overlapping oriented one-edge word paths must be attached
to the exact same marked old real centre, regardless of the
orientations in which the common formal edge was presented. -/
theorem privateFan_overlapping_unit_edges_same_centre
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (o o' : WordOccurrence S D)
    (p q : PathPosition S (occurrenceWord S D o))
    (p' q' : PathPosition S (occurrenceWord S D o'))
    (hLength : diversityLength S (occurrenceWord S D o) = 1)
    (hLength' : diversityLength S (occurrenceWord S D o') = 1)
    (hpq : pathAdjacent S (occurrenceWord S D o) p q)
    (hpq' : pathAdjacent S (occurrenceWord S D o') p' q')
    (hFirst : privateFanAtWordPosition S D centres o p =
      privateFanAtWordPosition S D centres o' p')
    (hSecond : privateFanAtWordPosition S D centres o q =
      privateFanAtWordPosition S D centres o' q') :
    toDistinctCentre sort centres o.1 =
      toDistinctCentre sort centres o'.1 := by
  have hPos : 0 < diversityLength S (occurrenceWord S D o) := by omega
  have hPos' : 0 < diversityLength S (occurrenceWord S D o') := by omega
  rcases unit_path_edge_has_start S (occurrenceWord S D o)
    hLength p q hpq with hp | hq
  · have hp' : p' = pathStart S (occurrenceWord S D o') := by
      apply (privateFanAt_is_root_iff_start S D centres o' p').mp
      calc
        privateFanAtWordPosition S D centres o' p' =
            privateFanAtWordPosition S D centres o p := hFirst.symm
        _ = privateFanRoot S D centres := by
          rw [hp]
          exact privateFanAt_start S D centres o
    have hqFin := unit_path_edge_other_is_finish S
      (occurrenceWord S D o) hLength p q hpq hp
    have hqFin' := unit_path_edge_other_is_finish S
      (occurrenceWord S D o') hLength' p' q' hpq' hp'
    exact privateFan_shared_finishes_same_centre S D centres
      o o' q q' hqFin hqFin' hPos hPos' hSecond
  · have hq' : q' = pathStart S (occurrenceWord S D o') := by
      apply (privateFanAt_is_root_iff_start S D centres o' q').mp
      calc
        privateFanAtWordPosition S D centres o' q' =
            privateFanAtWordPosition S D centres o q := hSecond.symm
        _ = privateFanRoot S D centres := by
          rw [hq]
          exact privateFanAt_start S D centres o
    have hpFin := unit_path_edge_other_is_finish S
      (occurrenceWord S D o) hLength q p
      ((pathAdjacent_symm S (occurrenceWord S D o) p q).mp hpq) hq
    have hpFin' := unit_path_edge_other_is_finish S
      (occurrenceWord S D o') hLength' q' p'
      ((pathAdjacent_symm S (occurrenceWord S D o') p' q').mp hpq') hq'
    exact privateFan_shared_finishes_same_centre S D centres
      o o' p p' hpFin hpFin' hPos hPos' hFirst

/-- The complete geometric overlap classification: distinct path
occurrences only share edges if BOTH paths are one-diversity-letter
spokes attached to the SAME actual original tagged centre.
Repeated menus and equal syntactic word strings are included. -/
theorem privateFan_different_overlapping_edges_same_direct_spoke
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (o o' : WordOccurrence S D)
    (hDifferent : o ≠ o')
    (p q : PathPosition S (occurrenceWord S D o))
    (p' q' : PathPosition S (occurrenceWord S D o'))
    (hpq : pathAdjacent S (occurrenceWord S D o) p q)
    (hpq' : pathAdjacent S (occurrenceWord S D o') p' q')
    (hFirst : privateFanAtWordPosition S D centres o p =
      privateFanAtWordPosition S D centres o' p')
    (hSecond : privateFanAtWordPosition S D centres o q =
      privateFanAtWordPosition S D centres o' q') :
    diversityLength S (occurrenceWord S D o) = 1 ∧
    diversityLength S (occurrenceWord S D o') = 1 ∧
    toDistinctCentre sort centres o.1 =
      toDistinctCentre sort centres o'.1 := by
  obtain (hSame | ⟨hl, hl'⟩) :=
    privateFan_overlapping_path_edges_same_or_direct S D centres
      o o' p q p' q' hpq hpq' hFirst hSecond
  · exact False.elim (hDifferent hSame)
  · exact ⟨hl, hl',
      privateFan_overlapping_unit_edges_same_centre S D centres
        o o' p q p' q' hl hl' hpq hpq' hFirst hSecond⟩

end CCO.RawExact
