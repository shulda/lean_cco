import CCO.PositiveWords

/-!
# B050 C27: honest reversal of positive original typed private words

The canonical marked-pair orientation need not agree with a simple
cycle's traversal. We construct the reverse using the real OLD
converse atom on EACH letter and prove BOTH exact represented RAW
converse and original SAP STRONG endpoint-profile opposite.

On an original same-sort symmetric source, every diversity atom is
its own converse, so a reversed whole word has literally the SAME
STRONG endpoint palette. This does not reverse or commute individual
letters arbitrarily, replace a RAW diagonal with STRONG identity,
assume original CCO, or use a quotient-reduct automorphism group.
-/

universe u v w t

namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

/-- Reverse a genuinely positive OLD typed word, retaining all its
original intermediate sorts in reverse order and replacing each
diversity atom with its actual OLD typed converse. -/
def originalPositiveWordReverse {i j : ι} :
    PositiveWord S i j → PositiveWord S j i
  | .single a => .single (S.conv a)
  | .cons a rest =>
      PositiveWord.append S
        (originalPositiveWordReverse rest) (.single (S.conv a))

/-- Real endpoint semantics, including possible diagonal outputs,
are reversed EXACTLY. This needs neither original SAP nor CCO,
and is stronger than merely reversing fine-atom STRONG profiles. -/
theorem originalPositiveWordReverse_represented {i j : ι}
    (word : PositiveWord S i j) :
    PositiveWord.represented S (originalPositiveWordReverse S word) =
      TRel.converse (PositiveWord.represented S word) := by
  induction word with
  | single a =>
      change S.atomRel (S.conv a) = TRel.converse (S.atomRel a)
      exact RawWord.atomRel_flip S a
  | cons a rest ih =>
      change PositiveWord.represented S
          (PositiveWord.append S
            (originalPositiveWordReverse S rest) (.single (S.conv a))) =
        TRel.converse
          (TRel.comp (S.atomRel a) (PositiveWord.represented S rest))
      rw [PositiveWord.represented_append S, ih]
      change TRel.comp
        (TRel.converse (PositiveWord.represented S rest))
        (S.atomRel (S.conv a)) =
        TRel.converse
          (TRel.comp (S.atomRel a) (PositiveWord.represented S rest))
      rw [RawWord.atomRel_flip S a]
      exact (TRel.converse_comp
        (S.atomRel a) (PositiveWord.represented S rest)).symm

/-- Typed opposite of one REAL atomic singleton is its genuine
old typed converse singleton, with no other atom or equality. -/
private theorem original_opposite_singleton {i j : ι}
    (a : S.Atom i j) :
    S.opposite ({a} : S.Menu i j) =
      ({S.conv a} : S.Menu j i) := by
  ext b
  change S.conv b = a ↔ b = S.conv a
  constructor
  · intro h
    calc
      b = S.conv (S.conv b) := (S.conv_invol b).symm
      _ = S.conv a := congrArg S.conv h
  · intro h
    subst b
    exact S.conv_invol a

/-- Exact OLD STRONG endpoint profile of the REVERSED positive typed
word; only genuine original AgeSAP supplies concatenation, while
typed Peirce/reversal of atom triangles is already proved in B001. -/
theorem originalPositiveWordReverse_profile
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i j : ι} (word : PositiveWord S i j) :
    PositiveWord.profile S (originalPositiveWordReverse S word) =
      S.opposite (PositiveWord.profile S word) := by
  induction word with
  | single a =>
      change ({S.conv a} : S.Menu _ _) =
        S.opposite ({a} : S.Menu _ _)
      exact (original_opposite_singleton S a).symm
  | cons a rest ih =>
      change PositiveWord.profile S
          (PositiveWord.append S
            (originalPositiveWordReverse S rest) (.single (S.conv a))) =
        S.opposite
          (S.product ({a} : S.Menu _ _) (PositiveWord.profile S rest))
      calc
        _ = S.product
              (PositiveWord.profile S (originalPositiveWordReverse S rest))
              ({S.conv a} : S.Menu _ _) :=
          PositiveWord.profile_append_of_SAP
            S H sap (originalPositiveWordReverse S rest) (.single (S.conv a))
        _ = S.product
              (S.opposite (PositiveWord.profile S rest))
              (S.opposite ({a} : S.Menu _ _)) := by
          rw [ih, original_opposite_singleton S a]
        _ = S.opposite
              (S.product ({a} : S.Menu _ _) (PositiveWord.profile S rest)) :=
          (S.product_opposite _ _).symm

/-- C27 SAME-SORT source specialization: reversing an original
positive word preserves its WHOLE old STRONG same-sort endpoint
profile exactly, even if the word passes through arbitrary other
original named sorts. This is why geometric cycle orientation can be
handled without a synthetic symmetric/reduct word assumption. -/
theorem originalPositiveWordReverse_same_sort_profile
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} (word : PositiveWord S i i) :
    PositiveWord.profile S (originalPositiveWordReverse S word) =
      PositiveWord.profile S word := by
  rw [originalPositiveWordReverse_profile S H sap word]
  ext a
  change S.conv a ∈ PositiveWord.profile S word ↔
      a ∈ PositiveWord.profile S word
  rw [S.symmetricLoop a]

end CCO.TerminalLattice
