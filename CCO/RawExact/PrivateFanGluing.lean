import CCO.RawExact.PrivateFanVertices
import Mathlib.Tactic

/-!
# B002 C12: glue each actual RAW word path to the ONE fan root and
the ONE literal old marked centre it belongs to

The endpoints of every positive reduced path are shared, but all
private internal positions remain indexed by their distinct word
occurrences. This is the genuine finite-vertex quotient that must
precede edge labelling and simple-cycle classification.

A zero-diversity word has coincident start and finish positions;
it is deliberately treated separately by ZeroWordHelly, not by
falsely gluing an equality edge between two distinct fan vertices.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {root : ι} {I : Type (max u v)} [Finite I]
variable {sort : I → ι}

def privateFanAtWordPosition
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (o : WordOccurrence S D)
    (p : PathPosition S (occurrenceWord S D o)) :
    PrivateFanVertex S D centres :=
  if hStart : p.val = 0 then
    privateFanRoot S D centres
  else if hFinish :
      p.val = diversityLength S (occurrenceWord S D o) then
    privateFanCentre S D centres (toDistinctCentre sort centres o.1)
  else
    privateFanInterior S D centres o ⟨p, hStart, hFinish⟩

/-- Every occurrence starts at the SAME formal root, even if
another word has exactly the same syntactic text. -/
theorem privateFanAt_start
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (o : WordOccurrence S D) :
    privateFanAtWordPosition S D centres o
      (pathStart S (occurrenceWord S D o)) =
      privateFanRoot S D centres := by
  simp [privateFanAtWordPosition, pathStart]

/-- At positive diversity length, the finish attaches to the
actual old centre, deduplicated across all menus with the same
tagged real centre value. -/
theorem privateFanAt_finish
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (o : WordOccurrence S D)
    (hPositive : 0 < diversityLength S (occurrenceWord S D o)) :
    privateFanAtWordPosition S D centres o
      (pathFinish S (occurrenceWord S D o)) =
      privateFanCentre S D centres (toDistinctCentre sort centres o.1) := by
  simp [privateFanAtWordPosition, pathFinish,
    Nat.ne_of_gt hPositive]

/-- The middle of a private path never becomes an existing centre or
the formal root. This is a statement about FORMAL vertices, not
about possible noninjectivity of a word realization into the source. -/
theorem privateFanAt_interior
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (o : WordOccurrence S D)
    (p : PathPosition S (occurrenceWord S D o))
    (hStart : p.val ≠ 0)
    (hFinish : p.val ≠ diversityLength S (occurrenceWord S D o)) :
    privateFanAtWordPosition S D centres o p =
      privateFanInterior S D centres o ⟨p, hStart, hFinish⟩ := by
  simp [privateFanAtWordPosition, hStart, hFinish]

/-- The root and all original marked centres have the correct
named source sort, including mixed-sort word families. -/
theorem privateFanSort_root
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t)) :
    privateFanSort S D centres (privateFanRoot S D centres) = root := rfl

theorem privateFanSort_occurrence_centre
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t)) (t : I) :
    privateFanSort S D centres
      (privateFanCentre S D centres (toDistinctCentre sort centres t)) =
      sort t := rfl

/-- A real centre is still injectively embedded as a marked formal
vertex; no two distinct actual old centre values have been merged. -/
def privateFanMarks
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t)) :
    DistinctCentres sort centres ↪ PrivateFanVertex S D centres :=
  ⟨privateFanCentre S D centres,
    privateFanCentre_injective S D centres⟩

end CCO.RawExact
