import CCO.RawExact.PathLocalDegree

/-!
# B002 C12/C26: private vertices cannot jump between RAW word paths

Each nonendpoint vertex belongs to exactly one occurrence, including
the actual menu index and the slot within its word list. The only
edges incident to that private vertex come from the SAME occurrence
and are the ordinary consecutive edges of its path. In particular,
it has no old-centre/old-centre edge.

This is the key isolation fact needed for proving that a simple
cycle traverses a whole private path rather than switching between
different occurrences at an internal vertex. No CCO or exact
Helly provider is assumed.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {root : ι} {I : Type (max u v)} [Finite I]
variable {sort : I → ι}

/-- If a glued position is somebody's PRIVATE interior, its word
occurrence must be precisely that private occurrence. -/
theorem privateFanAt_interior_occurrence
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (o : WordOccurrence S D)
    (p : PrivateInteriorPosition S D o)
    (o' : WordOccurrence S D)
    (q : PathPosition S (occurrenceWord S D o'))
    (h : privateFanAtWordPosition S D centres o' q =
      privateFanInterior S D centres o p) :
    o' = o := by
  unfold privateFanAtWordPosition at h
  split_ifs at h <;>
    simp_all [privateFanRoot, privateFanCentre, privateFanInterior]

/-- An actual private interior is not an old-centre graph endpoint. -/
theorem privateFanInterior_not_old_adjacent
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (o : WordOccurrence S D)
    (p : PrivateInteriorPosition S D o)
    (v : PrivateFanVertex S D centres) :
    ¬ privateFanOldCentreAdjacent S D centres
      (privateFanInterior S D centres o p) v := by
  rintro ⟨c, d, _, hStart, _⟩
  simp [privateFanCentre, privateFanInterior] at hStart

/-- Any fan edge OUT of an internal vertex comes from this same
occurrence and from a neighbouring finite position on that path. -/
theorem privateFanInterior_neighbours_only_own_path
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (o : WordOccurrence S D)
    (p : PrivateInteriorPosition S D o)
    (v : PrivateFanVertex S D centres)
    (hAdj : privateFanAdjacent S D centres
      (privateFanInterior S D centres o p) v) :
    ∃ q : PathPosition S (occurrenceWord S D o),
      pathAdjacent S (occurrenceWord S D o) p.1 q ∧
      v = privateFanAtWordPosition S D centres o q := by
  rcases hAdj with hOld | hPath
  · exact False.elim
      (privateFanInterior_not_old_adjacent S D centres o p v hOld)
  · rcases hPath with ⟨o', r, q, hrq, hr, hv⟩
    have hOccurrence : o' = o :=
      privateFanAt_interior_occurrence S D centres o p o' r hr.symm
    subst o'
    have hP : privateFanAtWordPosition S D centres o p.1 =
        privateFanInterior S D centres o p := by
      simpa using (privateFanAt_interior S D centres o p.1
        p.property.1 p.property.2)
    have hPosition : r = p.1 :=
      privateFanAtWordPosition_injective S D centres o
        (hr.symm.trans hP.symm)
    subst r
    exact ⟨q, hrq, hv⟩

end CCO.RawExact
