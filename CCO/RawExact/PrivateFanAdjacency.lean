import CCO.RawExact.PrivateFanGluing

/-!
# B002 C12/C26: undirected incidence of the actual private-word fan

The fan consists of a complete graph on the distinct old actual
centres, plus one finite path for EACH occurrence of a genuine RAW
word, with those paths glued only at the common formal root and at
the literal old centre to which they belong.

This is a concrete, source-independent adjacency predicate on the
proved finite private-fan carrier. Atom labelling, non-loopness
and simple-cycle classification remain separate C12 tasks.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {root : ι} {I : Type (max u v)} [Finite I]
variable {sort : I → ι}

/-- The centre graph contains every genuinely distinct pair of
actual old tagged centres. There is no edge on a diagonal. -/
def privateFanOldCentreAdjacent
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (v w : PrivateFanVertex S D centres) : Prop :=
  ∃ c d : DistinctCentres sort centres,
    c ≠ d ∧
    v = privateFanCentre S D centres c ∧
    w = privateFanCentre S D centres d

/-- Two formal fan vertices are adjacent along the same private
word occurrence exactly if some two neighbouring POSITIONS of that
particular word have been attached to those vertices. -/
def privateFanPathAdjacent
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (v w : PrivateFanVertex S D centres) : Prop :=
  ∃ (o : WordOccurrence S D)
      (p q : PathPosition S (occurrenceWord S D o)),
    pathAdjacent S (occurrenceWord S D o) p q ∧
    v = privateFanAtWordPosition S D centres o p ∧
    w = privateFanAtWordPosition S D centres o q

/-- Underlying undirected fan graph, before attaching its REAL
original atomic colour to each present edge. -/
def privateFanAdjacent
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (v w : PrivateFanVertex S D centres) : Prop :=
  privateFanOldCentreAdjacent S D centres v w ∨
  privateFanPathAdjacent S D centres v w

theorem privateFanOldCentreAdjacent_symm
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (v w : PrivateFanVertex S D centres) :
    privateFanOldCentreAdjacent S D centres v w ↔
      privateFanOldCentreAdjacent S D centres w v := by
  constructor
  · rintro ⟨c, d, hcd, hv, hw⟩
    exact ⟨d, c, hcd.symm, hw, hv⟩
  · rintro ⟨c, d, hcd, hv, hw⟩
    exact ⟨d, c, hcd.symm, hw, hv⟩

theorem privateFanPathAdjacent_symm
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (v w : PrivateFanVertex S D centres) :
    privateFanPathAdjacent S D centres v w ↔
      privateFanPathAdjacent S D centres w v := by
  constructor
  · rintro ⟨o, p, q, hpq, hv, hw⟩
    exact ⟨o, q, p,
      (pathAdjacent_symm S (occurrenceWord S D o) p q).mp hpq,
      hw, hv⟩
  · rintro ⟨o, p, q, hpq, hv, hw⟩
    exact ⟨o, q, p,
      (pathAdjacent_symm S (occurrenceWord S D o) p q).mp hpq,
      hw, hv⟩

theorem privateFanAdjacent_symm
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (v w : PrivateFanVertex S D centres) :
    privateFanAdjacent S D centres v w ↔
      privateFanAdjacent S D centres w v := by
  constructor
  · rintro (h | h)
    · exact Or.inl
        ((privateFanOldCentreAdjacent_symm S D centres v w).mp h)
    · exact Or.inr
        ((privateFanPathAdjacent_symm S D centres v w).mp h)
  · rintro (h | h)
    · exact Or.inl
        ((privateFanOldCentreAdjacent_symm S D centres w v).mp h)
    · exact Or.inr
        ((privateFanPathAdjacent_symm S D centres w v).mp h)

/-- Every pair of distinct actual marked centres has a genuine
old-centre graph edge; no choice of real lifts is involved. -/
theorem privateFan_centres_adjacent
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (c d : DistinctCentres sort centres)
    (hcd : c ≠ d) :
    privateFanAdjacent S D centres
      (privateFanCentre S D centres c)
      (privateFanCentre S D centres d) :=
  Or.inl ⟨c, d, hcd, rfl, rfl⟩

/-- The positive edges of every represented private RAW word
are present in the same finite fan graph, no matter how many
other identical word occurrences or repeated centres there are. -/
theorem privateFan_path_edge
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (o : WordOccurrence S D)
    (p q : PathPosition S (occurrenceWord S D o))
    (hpq : pathAdjacent S (occurrenceWord S D o) p q) :
    privateFanAdjacent S D centres
      (privateFanAtWordPosition S D centres o p)
      (privateFanAtWordPosition S D centres o q) :=
  Or.inr ⟨o, p, q, hpq, rfl, rfl⟩

end CCO.RawExact
