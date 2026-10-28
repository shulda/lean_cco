import CCO.RawExact.DirectEdgeMerging
import CCO.RawExact.WordOccurrences
import Mathlib.Tactic

/-!
# B002 C12: arbitrary identity-bearing one-edge RAW word restrictions

A private path with one genuine diversity edge need not be syntactically
`.atom a (.nil _)`: it may contain arbitrarily many genuine identity
letters. Erasing those letters normalizes it to exactly one original
typed atom, without erasing an identity OUTPUT of longer walks.

Consequently all duplicate direct root-to-same-actual-centre edges have
the same atom under the actual pairwise ball hypothesis, even when
their original words contained identities. This removes the last
syntactic restriction from the direct-edge-merging argument for C12.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

theorem zero_diversity_length_same_sort {i j : ι}
    (word : RawWord S i j) :
    diversityLength S word = 0 → i = j := by
  induction word with
  | nil i =>
      intro _
      rfl
  | identity tail ih =>
      exact ih
  | atom a tail ih =>
      intro h
      simp only [diversityLength] at h
      omega

theorem erase_zero_length_nil {i : ι}
    (word : RawWord S i i) :
    diversityLength S word = 0 →
      RawWord.eraseEquality S word = .nil i := by
  induction word with
  | nil i =>
      intro _
      rfl
  | identity tail ih =>
      exact ih
  | atom a tail ih =>
      intro h
      simp only [diversityLength] at h
      omega

/-- Precisely one diversity letter, regardless of the number and
location of genuine identity letters, is one actual typed atom after
identity erasure. The source and target sorts remain those of the word. -/
theorem erase_one_length_atom {i j : ι}
    (word : RawWord S i j) :
    diversityLength S word = 1 →
      ∃ a : S.Atom i j,
        RawWord.eraseEquality S word = .atom a (.nil j) := by
  induction word with
  | nil i =>
      intro h
      simp only [diversityLength] at h
      omega
  | identity tail ih =>
      exact ih
  | atom a tail ih =>
      intro h
      have hTail : diversityLength S tail = 0 := by
        change diversityLength S tail + 1 = 1 at h
        omega
      have hEq := zero_diversity_length_same_sort S tail hTail
      cases hEq
      have hNil := erase_zero_length_nil S tail hTail
      refine ⟨a, ?_⟩
      simpa only [RawWord.eraseEquality, hNil]

/-- A one-diversity-edge RAW word, including arbitrary identity
letters, represents exactly one genuine old atomic relation. -/
theorem one_length_word_is_atom {i j : ι}
    (word : RawWord S i j)
    (hLength : diversityLength S word = 1) :
    ∃ a : S.Atom i j,
      RawWord.relation S word = S.atomRel a := by
  obtain ⟨a, ha⟩ := erase_one_length_atom S word hLength
  refine ⟨a, ?_⟩
  calc
    RawWord.relation S word =
        RawWord.relation S (RawWord.eraseEquality S word) :=
      (RawWord.relation_eraseEquality S word).symm
    _ = RawWord.relation S (.atom a (.nil j)) := by rw [ha]
    _ = S.atomRel a := direct_word_is_atom S a

/-- The full N05 duplicate-edge consistency statement for *all*
length-one private path occurrences. Pairwise ball intersections,
including a menu with itself, force the same actual atom on two
direct edges to one tagged old centre. -/
theorem duplicate_reduced_direct_edges_agree
    {root : ι} {I : Type (max u v)} [Finite I]
    (sort : I → ι)
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (hPair : ∀ p q : I,
      (ball (evaluate S (D p).words) (centres p) ∩
        ball (evaluate S (D q).words) (centres q)).Nonempty)
    (p q : WordOccurrence S D)
    (hp : diversityLength S (occurrenceWord S D p) = 1)
    (hq : diversityLength S (occurrenceWord S D q) = 1)
    (hCentre : taggedCentre sort centres p.1 =
      taggedCentre sort centres q.1) :
    ∃ (a : S.Atom root (sort p.1))
      (b : S.Atom root (sort q.1)),
      RawWord.relation S (occurrenceWord S D p) = S.atomRel a ∧
      RawWord.relation S (occurrenceWord S D q) = S.atomRel b ∧
      (⟨taggedCentre sort centres p.1, a⟩ : AtomicBallRequest S root) =
        ⟨taggedCentre sort centres q.1, b⟩ := by
  obtain ⟨a, ha⟩ := one_length_word_is_atom S
    (occurrenceWord S D p) hp
  obtain ⟨b, hb⟩ := one_length_word_is_atom S
    (occurrenceWord S D q) hq
  obtain ⟨x, hxP, hxQ⟩ := hPair p.1 q.1
  have hAtomP : S.atomRel a x (centres p.1) := by
    have hw := occurrenceWord_of_ball S D centres p x hxP
    rw [ha] at hw
    exact hw
  have hAtomQ : S.atomRel b x (centres q.1) := by
    have hw := occurrenceWord_of_ball S D centres q x hxQ
    rw [hb] at hw
    exact hw
  exact ⟨a, b, ha, hb,
    request_eq_of_same_centre_and_common_point S
      ⟨taggedCentre sort centres p.1, a⟩
      ⟨taggedCentre sort centres q.1, b⟩
      hCentre ⟨x, hAtomP, hAtomQ⟩⟩

end CCO.RawExact
