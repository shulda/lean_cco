import CCO.RawExact.WordPathPositions
import CCO.RawExact.OccurrenceRealizations

/-!
# B002 C12: alter only TWO reference RAW walks at one common old root

For an arbitrary finite family of pairwise-intersecting nonempty
exact balls, two chosen word occurrences may be given genuine
old-real witnesses with the SAME source point and their prescribed
literal old centres as targets.

All other occurrences keep their separately selected reference
walks, whose starting points may be entirely different. The
existence of a family in which ALL occurrences start at one point
is exactly the unproved C13 conclusion, and is not assumed here.

This controlled two-occurrence replacement is the combinatorial
basis for proving each simple fan cycle has a source homomorphism
without classifying every cycle's entire private path traversal.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- One actual independently chosen represented RAW word walk for
EVERY original occurrence; only each literal old centre is fixed. -/
abbrev FanWalkChoices
    {root : ι} {I : Type (max u v)} [Finite I]
    {sort : I → ι}
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t)) :=
  ∀ o : WordOccurrence S D,
    Σ x : X root, WordPath S (occurrenceWord S D o) x (centres o.1)

/-- The previously proved independent reference witnesses provide
a family of actual walks without any simultaneous-root premise. -/
noncomputable def referenceFanWalkChoices
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    {root : ι} {I : Type (max u v)} [Finite I]
    {sort : I → ι}
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t)) :
    FanWalkChoices S D centres :=
  fun o => referenceOccurrenceWalk S H D centres o

/-- Given any two original RAW word occurrences, change ONLY those
two paths to a common actual old root supplied by the pairwise
ball intersection hypothesis. All remaining word paths retain
their old independent witnesses. The two occurrences may be equal
or belong to the same menu or the same actual old centre. -/
theorem choose_fan_walks_with_two_common_roots
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
    ∃ (x : X root) (choice : FanWalkChoices S D centres),
      (choice p).1 = x ∧ (choice q).1 = x := by
  classical
  obtain ⟨⟨x, wp, wq⟩⟩ :=
    pair_private_walks_of_pairwise_balls S D centres hPair p q
  let choice : FanWalkChoices S D centres := fun o => by
    by_cases hp : o = p
    · subst o
      exact ⟨x, wp⟩
    · by_cases hq : o = q
      · subst o
        exact ⟨x, wq⟩
      · exact referenceOccurrenceWalk S H D centres o
  have hAtP : (choice p).1 = x := by
    dsimp [choice]
    simp
  refine ⟨x, choice, hAtP, ?_⟩
  by_cases hpq : q = p
  · rw [hpq]
    exact hAtP
  · dsimp [choice]
    simp [hpq]

end CCO.RawExact
