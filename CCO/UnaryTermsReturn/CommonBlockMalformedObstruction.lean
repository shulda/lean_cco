import CCO.UnaryTermsReturn.CommonBlockSourceCertificate
import Mathlib.Data.Set.Card
import Lean.Elab.Tactic.Omega

/-!
# B052 C17–C21: unbounded closed-substructure obstruction, no hidden HN shortcut

For the ACTUAL old SAP+semantic-CCO two-sort common-block structure,
the quotient-only malformed n-cycle has two Fin n carriers and the
genuine named inverse transition pair, with the second direction
rotated by one. All unary-closed nonempty substructures are the full
two-sort 2n-point source, hence the whole source is irreducible in the
unary-functional free-amalgam sense.

For each proposed bound N choose n=N+2. The only unary-closed
substructures of total size at most N are empty, although the
whole cycle has 2n>N points and has NO homomorphism-embedding into
an actual completed hidden quotient member: inverse named
transitions force collapse of distinct x_i.

The negative example is *not* unary-admissible. It is a diagnostic
for arbitrary total-unary partial inputs, not a counterexample to
the source10 restricted Ramsey/HN applicability result.
-/

namespace CCO.UnaryTermsReturn

/-- An actual two-sort unary-closed fragment which has even one
vertex must contain the WHOLE cyclic source. In particular
there are no nonempty proper unary-closed substructures for
any n>=2, irrespective of the absence of displayed orbitals. -/
theorem malformed_cycle_no_nonempty_proper_closed
    {n : Nat} (hn : 2 ≤ n) (A B : Set (Fin n))
    (hClosed : MalformedCycleClosed A B)
    (hNonempty : A.Nonempty ∨ B.Nonempty) :
    A = Set.univ ∧ B = Set.univ :=
  malformed_cycle_closed_nonempty_is_full hn A B hClosed hNonempty

/-- Every proper closed fragment of the malformed cycle has
both quotient sorts empty. This is the unary irreducibility
obstruction underlying C18, not a graph-edge argument. -/
theorem malformed_cycle_proper_closed_empty
    {n : Nat} (hn : 2 ≤ n) (A B : Set (Fin n))
    (hClosed : MalformedCycleClosed A B)
    (hProper : A ≠ Set.univ ∨ B ≠ Set.univ) :
    A = ∅ ∧ B = ∅ := by
  by_contra h
  have hNonempty : A.Nonempty ∨ B.Nonempty := by
    by_contra hEmpty
    push_neg at hEmpty
    have ha : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hEmpty.1
    have hb : B = ∅ := Set.not_nonempty_iff_eq_empty.mp hEmpty.2
    exact h ⟨ha,hb⟩
  obtain ⟨ha,hb⟩ :=
    malformed_cycle_closed_nonempty_is_full hn A B hClosed hNonempty
  rcases hProper with hA | hB
  · exact hA ha
  · exact hB hb

/-- Uniform obstruction-window failure in the sharp source10
sense: for every N there is an actual n>=2 malformed
partial cycle of 2n>N vertices, and NO nonempty unary-closed
substructure of total size <=N. The standard original
common-block source is independently SAP+CCO; the whole
malformed source is not homomorphism-embedding completable. -/
theorem commonBlockMalformed_no_uniform_closed_obstruction
    (N : Nat) :
    AgeSAP commonBlockOriginalAtomicSource ∧
    SemanticCCO.{0,0,0,0} commonBlockOriginalAtomicSource ∧
    ∃ n : Nat, 2 ≤ n ∧
      N < Fintype.card (Fin n ⊕ Fin n) ∧
      (∀ A B : Set (Fin n),
        MalformedCycleClosed A B →
        A.ncard + B.ncard ≤ N →
        A = ∅ ∧ B = ∅) ∧
      (∀ imageA : Fin n → Quotient (commonBlockOldSetoid false),
        ∀ imageB : Fin n → Quotient (commonBlockOldSetoid true),
          (∀ i, imageB i = commonBlockForward (imageA i)) →
          (∀ i, imageA (malformedCycleStep n i) =
            commonBlockBackward (imageB i)) →
          ¬ Function.Injective imageA) := by
  refine ⟨commonBlockOriginalAgeSAP,
    commonBlockOriginalSemanticCCO, ?_⟩
  let n := N + 2
  have hn : 2 ≤ n := by omega
  have hlarge : N < Fintype.card (Fin n ⊕ Fin n) := by
    rw [malformed_cycle_carrier_card]
    omega
  refine ⟨n, hn, hlarge, ?_, ?_⟩
  · intro A B hClosed hSmall
    by_cases hEmpty : A.Nonempty ∨ B.Nonempty
    · obtain ⟨ha,hb⟩ :=
        malformed_cycle_closed_nonempty_is_full hn A B
          hClosed hEmpty
      have hc : A.ncard + B.ncard = 2 * n := by
        rw [ha,hb]
        simp [Set.ncard_univ, Nat.two_mul]
      omega
    · push_neg at hEmpty
      exact ⟨Set.not_nonempty_iff_eq_empty.mp hEmpty.1,
        Set.not_nonempty_iff_eq_empty.mp hEmpty.2⟩
  · intro imageA imageB hf hg
    exact common_block_malformed_cycle_no_injective_realization
      hn imageA imageB hf hg

end CCO.UnaryTermsReturn
