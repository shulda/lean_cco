import CCO.RawExact.FanDirectCoincidence
import CCO.RawExact.ReducedDirectWords

/-!
# B002 C12: actual atomic-colour coherence of overlapping private spokes

Geometric edge-overlap classification and represented RAW-word
normalization combine to prove that ANY TWO distinct occurrences
attributing the same ordered formal fan edge produce precisely the
same genuine original atomic request. This includes identity-padded
one-step words, repeated actual centres and multiple list slots
inside a single exact menu.

The proof uses the given pairwise intersection of actual nonempty
exact balls, not CCO, SAP or the still-open general ball Helly theorem.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- This is the direct-spoke label coherence needed to glue
all private path-edge labels into a SINGLE old-coloured fan.
If two different occurrences happen to present the SAME formal
direct edge, their normalized original atom request is equal. -/
theorem privateFan_overlapping_different_edges_same_atomic_request
    {root : ι} {I : Type (max u v)} [Finite I]
    (sort : I → ι)
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (hPair : ∀ p q : I,
      (ball (evaluate S (D p).words) (centres p) ∩
        ball (evaluate S (D q).words) (centres q)).Nonempty)
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
    ∃ (a : S.Atom root (sort o.1))
      (b : S.Atom root (sort o'.1)),
      RawWord.relation S (occurrenceWord S D o) = S.atomRel a ∧
      RawWord.relation S (occurrenceWord S D o') = S.atomRel b ∧
      (⟨taggedCentre sort centres o.1, a⟩ : AtomicBallRequest S root) =
        ⟨taggedCentre sort centres o'.1, b⟩ := by
  obtain ⟨hLength, hLength', hCentres⟩ :=
    privateFan_different_overlapping_edges_same_direct_spoke
      S D centres o o' hDifferent p q p' q' hpq hpq' hFirst hSecond
  have hTagged :
      taggedCentre sort centres o.1 =
        taggedCentre sort centres o'.1 := by
    simpa only [toDistinctCentre] using congrArg Subtype.val hCentres
  exact duplicate_reduced_direct_edges_agree S sort D centres
    hPair o o' hLength hLength' hTagged

end CCO.RawExact
