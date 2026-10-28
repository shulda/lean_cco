import CCO.RawExact.QuotientExpansionOverlaps
import CCO.RawExact.WordPathPositions

/-!
# Real reference walks for a quotient path expansion

Choose ONE real endpoint pair for the full nonempty menu of each marked
edge, then choose an actual walk for every word occurrence of that menu.
Thus duplicate direct words use the same real endpoints and necessarily
have the same actual colour. Different marked edges need no simultaneous
real realization at this stage.
-/

universe u v w

namespace CCO.RawExact.QuotientExpansion

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {n : Nat} (sort : Fin n → ι) (P : Menus S sort)
variable (hNonempty : ∀ e, TRel.Nonempty (evaluate S (P e)))

noncomputable def referenceLeft (e : Edge n) : X (sort (left e)) :=
  (hNonempty e).choose

noncomputable def referenceRight (e : Edge n) : X (sort (right e)) :=
  (hNonempty e).choose_spec.choose

theorem referencePair_valid (e : Edge n) :
    evaluate S (P e) (referenceLeft S sort P hNonempty e)
      (referenceRight S sort P hNonempty e) :=
  (hNonempty e).choose_spec.choose_spec

noncomputable def referenceWalk (o : Occurrence S sort P) :
    WordPath S (word S sort P o)
      (referenceLeft S sort P hNonempty o.1)
      (referenceRight S sort P hNonempty o.1) :=
  Classical.choice ((wordPath_iff_relation S (word S sort P o) _ _).mpr
    (referencePair_valid S sort P hNonempty o.1 (word S sort P o) (List.get_mem _ _)))

noncomputable def referencePoint (o : Occurrence S sort P)
    (p : PathPosition S (word S sort P o)) : Sigma X :=
  wordPathPointAt S (referenceWalk S sort P hNonempty o) p

theorem referencePoint_start (o : Occurrence S sort P) :
    referencePoint S sort P hNonempty o (pathStart S (word S sort P o)) =
      (⟨sort (left o.1), referenceLeft S sort P hNonempty o.1⟩ : Sigma X) :=
  wordPathPointAt_start S _

theorem referencePoint_finish (o : Occurrence S sort P) :
    referencePoint S sort P hNonempty o (pathFinish S (word S sort P o)) =
      (⟨sort (right o.1), referenceRight S sort P hNonempty o.1⟩ : Sigma X) :=
  wordPathPointAt_finish S _

theorem referencePoint_sort (o : Occurrence S sort P)
    (p : PathPosition S (word S sort P o)) :
    (referencePoint S sort P hNonempty o p).1 =
      vertexSort S sort P (atPosition S sort P o p) :=
  (wordPathPointAt_sort S _ p).trans (at_sort S sort P o p).symm

theorem referencePoint_genuine (o : Occurrence S sort P)
    (p q : PathPosition S (word S sort P o))
    (h : pathAdjacent S (word S sort P o) p q) :
    GenuineEdge S (referencePoint S sort P hNonempty o p)
      (referencePoint S sort P hNonempty o q) :=
  wordPathPointAt_genuine_adjacent S _ p q h

/-- All words for the same marked edge share exactly their actual
reference endpoint points, whichever orientation is displayed. -/
theorem reference_marked_point_eq
    (o o' : Occurrence S sort P) (hEdge : o.1 = o'.1)
    (p : PathPosition S (word S sort P o))
    (p' : PathPosition S (word S sort P o')) (m : Fin n)
    (hp : mark S sort P m = atPosition S sort P o p)
    (hp' : mark S sort P m = atPosition S sort P o' p') :
    referencePoint S sort P hNonempty o p =
      referencePoint S sort P hNonempty o' p' := by
  rcases o with ⟨e, slot⟩
  rcases o' with ⟨e', slot'⟩
  change e = e' at hEdge
  subst e'
  rcases mark_position_endpoint S sort P ⟨e, slot⟩ p m hp with h | h <;>
    rcases mark_position_endpoint S sort P ⟨e, slot'⟩ p' m hp' with h' | h'
  · have hpStart : p = pathStart S (word S sort P ⟨e, slot⟩) := Fin.ext h.1
    have hpStart' : p' = pathStart S (word S sort P ⟨e, slot'⟩) := Fin.ext h'.1
    rw [hpStart, hpStart', referencePoint_start, referencePoint_start]
  · exact False.elim (left_ne_right e (h.2.symm.trans h'.2))
  · exact False.elim (left_ne_right e (h'.2.symm.trans h.2))
  · have hpFinish : p = pathFinish S (word S sort P ⟨e, slot⟩) := Fin.ext h.1
    have hpFinish' : p' = pathFinish S (word S sort P ⟨e, slot'⟩) := Fin.ext h'.1
    rw [hpFinish, hpFinish', referencePoint_finish, referencePoint_finish]

/-- Genuine colour compatibility on EVERY overlapping oriented
private edge, including duplicate identity-padded direct words. -/
theorem overlapping_edge_reference_colours
    (o o' : Occurrence S sort P)
    (p q : PathPosition S (word S sort P o))
    (p' q' : PathPosition S (word S sort P o'))
    (hpq : pathAdjacent S (word S sort P o) p q)
    (hpq' : pathAdjacent S (word S sort P o') p' q')
    (hp : atPosition S sort P o p = atPosition S sort P o' p')
    (hq : atPosition S sort P o q = atPosition S sort P o' q') :
    taggedColour S (referencePoint S sort P hNonempty o p)
      (referencePoint S sort P hNonempty o q) =
      taggedColour S (referencePoint S sort P hNonempty o' p')
        (referencePoint S sort P hNonempty o' q') := by
  by_cases hSame : o = o'
  · subst o'
    have hpp' := at_injective S sort P o hp
    have hqq' := at_injective S sort P o hq
    subst p'
    subst q'
    rfl
  · have hEdge := (different_overlapping_edges_are_same_direct_edge
      S sort P o o' hSame p q p' q' hpq hpq' hp hq).1
    obtain ⟨m, hm⟩ := shared_position_is_marked S sort P o o' hSame p p' hp
    obtain ⟨r, hr⟩ := shared_position_is_marked S sort P o o' hSame q q' hq
    have hPointP := reference_marked_point_eq S sort P hNonempty o o' hEdge
      p p' m hm.symm (hm.symm.trans hp)
    have hPointQ := reference_marked_point_eq S sort P hNonempty o o' hEdge
      q q' r hr.symm (hr.symm.trans hq)
    rw [hPointP, hPointQ]

end CCO.RawExact.QuotientExpansion
