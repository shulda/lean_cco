import CCO.UnaryTermsReturn.CommonBlockAgeSAP
import CCO.UnaryTermsReturn.CommonBlockSemanticCCO
import CCO.UnaryTermsReturn.CommonBlockMalformed

/-!
# B052 C16–C21: genuine old SAP+CCO alongside unbounded malformed cycles

This is the source10 diagnostic assembled over ONE ACTUAL old atomic
two-sort common-block structure, not an arbitrary pair of functions.

The original old age has strong amalgamation by an explicit finite
induced pushout and has semantic cycle-constrainedness by the actual
block-label cycle model. Nevertheless the separately displayed
quotient-only partial sources may have arbitrarily large irreducible
one-generator closures and do NOT admit injective named-transition
representations into genuine completed old hidden quotients.

The sharp obstruction is only for arbitrary total-unary PARTIAL
inputs: these cycles fail unary-admissibility. Nothing here assumes
hidden hereditary SAP or supplies an external HN theorem.
-/

namespace CCO.UnaryTermsReturn

open CCO

/-- The *same* concrete original source satisfies BOTH OLD age
strong amalgamation and semantic CCO, as required by source10's
malformed-cycle counterexample. Neither property is a new premise. -/
theorem commonBlockOriginalSAPandCCO :
    AgeSAP commonBlockOriginalAtomicSource ∧
      SemanticCCO.{0,0,0,0} commonBlockOriginalAtomicSource :=
  ⟨commonBlockOriginalAgeSAP, commonBlockOriginalSemanticCCO⟩

/-- Source10 C16–C21 in a single genuine old-model statement:
for EVERY finite obstruction threshold N, the same OLD SAP+CCO
source admits a malformed two-hidden-sort total-unary cycle
of length 2n>N. Every nonempty functionally closed subdiagram
is the entire cyclic source, and ANY map preserving the ACTUAL
inverse old quotient transition pair collapses distinct
quotient vertices. In particular the whole irreducible cycle
has no homomorphism-embedding into an actual completed member.

The statement does not call the cycles unary-admissible, does
not turn an old source into an arbitrary hidden-SAP provider,
and does not treat a negative diagnostic as an HN receiving theorem. -/
theorem commonBlockSAPCCO_unbounded_malformed_cycle
    (N : Nat) :
    AgeSAP commonBlockOriginalAtomicSource ∧
    SemanticCCO.{0,0,0,0} commonBlockOriginalAtomicSource ∧
    ∃ n : Nat, 2 ≤ n ∧ N < Fintype.card (Fin n ⊕ Fin n) ∧
      (∀ A B : Set (Fin n),
        MalformedCycleClosed A B →
        (A.Nonempty ∨ B.Nonempty) →
        A = Set.univ ∧ B = Set.univ) ∧
      (∀ imageA : Fin n → Quotient (commonBlockOldSetoid false),
        ∀ imageB : Fin n → Quotient (commonBlockOldSetoid true),
          (∀ i, imageB i = commonBlockForward (imageA i)) →
          (∀ i, imageA (malformedCycleStep n i) =
            commonBlockBackward (imageB i)) →
          ¬ Function.Injective imageA) := by
  refine ⟨commonBlockOriginalAgeSAP, commonBlockOriginalSemanticCCO, ?_⟩
  obtain ⟨n, hn, hsize⟩ := malformed_cycle_arbitrarily_large N
  refine ⟨n, hn, hsize, ?_, ?_⟩
  · intro A B hClosed hNonempty
    exact malformed_cycle_closed_nonempty_is_full
      hn A B hClosed hNonempty
  · intro imageA imageB hf hg
    exact common_block_malformed_cycle_no_injective_realization
      hn imageA imageB hf hg

end CCO.UnaryTermsReturn
