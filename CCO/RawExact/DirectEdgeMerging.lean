import CCO.RawExact.AtomicFanDuplicates
import CCO.RawExact.AtomicExact

/-!
# B002 C12: genuinely merge duplicate private length-one edges

Two distinct RAW word occurrences may give the SAME root--old-centre
edge in a private-path fan. If their centre values coincide, the
witnessed pairwise intersection of the containing exact balls forces
their original atomic colours to coincide. There is consequently one
valid simple graph edge, not two parallel edges or a fake 2-cycle.

No original CCO/Helly assumption is used: the pairwise ball witnesses
are given by the theorem's explicit source hypothesis.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- The full actual root-to-centre atomic colour of a singleton
RAW positive-letter word, with the trailing genuine identity. -/
theorem direct_word_is_atom {i j : ι} (a : S.Atom i j) :
    RawWord.relation S (.atom a (.nil j)) = S.atomRel a := by
  calc
    RawWord.relation S (.atom a (.nil j)) =
      evaluate S [RawWord.atom a (.nil j)] :=
      (evaluate_single S _).symm
    _ = S.atomRel a := atomic_word_relation S a

/-- Repeated actual centre values force equal original atomic
colours for length-one word occurrences of pairwise-compatible
exact balls, including two words from the SAME exact menu. -/
theorem duplicate_direct_edges_agree
    {root : ι} {I : Type (max u v)}
    (sort : I → ι)
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (hPair : ∀ p q : I,
      (ball (evaluate S (D p).words) (centres p) ∩
        ball (evaluate S (D q).words) (centres q)).Nonempty)
    (p q : I)
    (a : S.Atom root (sort p))
    (b : S.Atom root (sort q))
    (ha : RawWord.atom a (.nil _) ∈ (D p).words)
    (hb : RawWord.atom b (.nil _) ∈ (D q).words)
    (hTagged : taggedCentre sort centres p =
      taggedCentre sort centres q) :
    (⟨taggedCentre sort centres p, a⟩ : AtomicBallRequest S root) =
      (⟨taggedCentre sort centres q, b⟩ : AtomicBallRequest S root) := by
  obtain ⟨x, hp, hq⟩ := hPair p q
  have hAtomP : S.atomRel a x (centres p) := by
    have hw := hp (RawWord.atom a (.nil _)) ha
    rw [direct_word_is_atom S a] at hw
    exact hw
  have hAtomQ : S.atomRel b x (centres q) := by
    have hw := hq (RawWord.atom b (.nil _)) hb
    rw [direct_word_is_atom S b] at hw
    exact hw
  exact request_eq_of_same_centre_and_common_point S
    ⟨taggedCentre sort centres p, a⟩
    ⟨taggedCentre sort centres q, b⟩
    hTagged ⟨x, hAtomP, hAtomQ⟩

end CCO.RawExact
