import CCO.RawExact.PrivateFanSimple

/-!
# B002 C12: exact incidence of the one formal fan root

The global target root cannot participate in old-centre edges.
If it lies on a private-word edge, that edge must be the FIRST
genuine diversity edge of precisely one actual word occurrence.
Identity-only words contribute no such edge.

This is the combinatorial root-incidence fact needed to identify
the TWO private paths traversed by a simple fan cycle containing
the root. There is no CCO, Helly or SAP hypothesis here.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {root : ι} {I : Type (max u v)} [Finite I]
variable {sort : I → ι}

/-- A glued position is the one global root iff it is the initial
zero position of its RAW word occurrence. -/
theorem privateFanAt_is_root_iff_start
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (o : WordOccurrence S D)
    (p : PathPosition S (occurrenceWord S D o)) :
    privateFanAtWordPosition S D centres o p =
      privateFanRoot S D centres ↔
    p = pathStart S (occurrenceWord S D o) := by
  constructor
  · intro h
    have hFirst := privateFanAt_start S D centres o
    exact privateFanAtWordPosition_injective S D centres o
      (h.trans hFirst.symm)
  · rintro rfl
    exact privateFanAt_start S D centres o

/-- The global formal root has NO edge belonging to the complete
old-centre subdiagram. It touches private words only. -/
theorem privateFan_root_not_old_adjacent
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (v : PrivateFanVertex S D centres) :
    ¬ privateFanOldCentreAdjacent S D centres
      (privateFanRoot S D centres) v := by
  rintro ⟨c, d, _, hRoot, _⟩
  exact (privateFanRoot_ne_centre S D centres c) hRoot

/-- An arbitrary fan edge incident to the formal root is the
FIRST step of some positive-length RAW word occurrence. This
retains both word and list-slot indexes even for duplicated words. -/
theorem privateFan_root_edges_are_first_steps
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (v : PrivateFanVertex S D centres)
    (hAdj : privateFanAdjacent S D centres
      (privateFanRoot S D centres) v) :
    ∃ (o : WordOccurrence S D)
      (q : PathPosition S (occurrenceWord S D o)),
      q.val = 1 ∧
      v = privateFanAtWordPosition S D centres o q := by
  rcases hAdj with hOld | hPath
  · exact False.elim (privateFan_root_not_old_adjacent S D centres v hOld)
  · obtain ⟨o, p, q, hpq, hRoot, hv⟩ := hPath
    have hp : p = pathStart S (occurrenceWord S D o) :=
      (privateFanAt_is_root_iff_start S D centres o p).mp hRoot.symm
    subst p
    exact ⟨o, q,
      (pathAdjacent_start_iff S (occurrenceWord S D o) q).mp hpq, hv⟩

end CCO.RawExact
