import CCO.RawExact.FanRootIncidence
import CCO.RawExact.PathEndpointEdges

/-!
# B002 C12: the only private edges touching old marked centres

Every positive private path is attached at exactly one old marked
centre: its own occurrence's literal actual tagged centre. If a
formal path position reaches ANY marked centre, it must be the
last position of that path and the centres must be the same
ACTUAL tagged real point. Different sort names are never confused.

Together with the root-incidence theorem, this isolates the two
places where a simple fan cycle can enter/leave a private path.
No Helly or CCO provider is introduced.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {root : ι} {I : Type (max u v)} [Finite I]
variable {sort : I → ι}

/-- On a positive-length private word, reaching its own old
centre is equivalent to being at the last formal path position. -/
theorem privateFanAt_own_centre_iff_finish
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (o : WordOccurrence S D)
    (hPositive : 0 < diversityLength S (occurrenceWord S D o))
    (p : PathPosition S (occurrenceWord S D o)) :
    privateFanAtWordPosition S D centres o p =
      privateFanCentre S D centres
        (toDistinctCentre sort centres o.1) ↔
    p = pathFinish S (occurrenceWord S D o) := by
  constructor
  · intro h
    have hLast := privateFanAt_finish S D centres o hPositive
    exact privateFanAtWordPosition_injective S D centres o
      (h.trans hLast.symm)
  · rintro rfl
    exact privateFanAt_finish S D centres o hPositive

/-- An arbitrary old marked centre is reached by a private word
only at the finish, and only if it is that occurrence's own
actual centre. Identity-only words never reach any old marked
centre, because their single formal position is the root. -/
theorem privateFanAt_old_centre_only_at_finish
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (o : WordOccurrence S D)
    (p : PathPosition S (occurrenceWord S D o))
    (c : DistinctCentres sort centres)
    (h : privateFanAtWordPosition S D centres o p =
      privateFanCentre S D centres c) :
    ∃ hPositive : 0 < diversityLength S (occurrenceWord S D o),
      p = pathFinish S (occurrenceWord S D o) ∧
      toDistinctCentre sort centres o.1 = c := by
  by_cases hFirst : p.val = 0
  · have hp : p = pathStart S (occurrenceWord S D o) :=
      Fin.ext hFirst
    rw [hp, privateFanAt_start S D centres o] at h
    exact False.elim
      ((privateFanRoot_ne_centre S D centres c) h)
  · by_cases hLast :
        p.val = diversityLength S (occurrenceWord S D o)
    · have hp : p = pathFinish S (occurrenceWord S D o) :=
        Fin.ext hLast
      have hPositive : 0 < diversityLength S (occurrenceWord S D o) := by
        omega
      rw [hp, privateFanAt_finish S D centres o hPositive] at h
      have hc := privateFanCentre_injective S D centres h
      exact ⟨hPositive, hp, hc⟩
    · rw [privateFanAt_interior S D centres o p hFirst hLast] at h
      simp [privateFanInterior, privateFanCentre] at h

/-- Every private-word edge incident to any old marked centre
is a LAST path step; the occurrence's centre is precisely the
given actual marked centre, including repeated menu indices. -/
theorem privateFan_centre_path_edges_are_last_steps
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (c : DistinctCentres sort centres)
    (v : PrivateFanVertex S D centres)
    (hAdj : privateFanPathAdjacent S D centres v
      (privateFanCentre S D centres c)) :
    ∃ (o : WordOccurrence S D)
      (p q : PathPosition S (occurrenceWord S D o)),
      q = pathFinish S (occurrenceWord S D o) ∧
      toDistinctCentre sort centres o.1 = c ∧
      pathAdjacent S (occurrenceWord S D o) p q ∧
      v = privateFanAtWordPosition S D centres o p := by
  obtain ⟨o, p, q, hpq, hv, hc⟩ := hAdj
  obtain ⟨_, hq, hCentre⟩ :=
    privateFanAt_old_centre_only_at_finish S D centres o q c hc.symm
  exact ⟨o, p, q, hq, hCentre, hpq, hv⟩

end CCO.RawExact
