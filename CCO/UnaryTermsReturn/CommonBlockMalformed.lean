import CCO.UnaryTermsReturn.CommonBlockModel
import CCO.UnaryTermsReturn.MalformedCycleCollapse

/-!
# B052 source10 C16–C21: actual old common-block model versus malformed cycles

The ACTUAL two-original-sort common-block atomic source is constructed
in CommonBlockModel. It has true quotient objects Q_A and Q_B and
actual inverse same-block quotient transitions. The malformed
total-unary partial source has a cyclic twist in the second
named transition, so it cannot inject into ANY completed hidden
diagram of this genuine old quotient model.

The failure is not a counterexample to unary-admissibility: its
full one-generator unary closure is the entire irreducible cycle
and has no embedding into a genuine completed source.

Old age SAP and semantic CCO for the source are separate open
C16 obligations, not inferred from this elementary quotient
function calculation or an external HN theorem.
-/

namespace CCO.UnaryTermsReturn

/-- Under the REAL source's ACTUAL named inverse quotient
functions (no arbitrary pseudo-functions), a malformed
two-sort n-cycle for n>=2 cannot have an injective
function-preserving image in the genuine original quotient
coordinates. This is the concrete C16/C19 witness.
No condition on the size of the ambient quotient sets. -/
theorem common_block_malformed_cycle_no_injective_realization
    {n : Nat} (hn : 2 ≤ n)
    (imageA : Fin n → Quotient (commonBlockOldSetoid false))
    (imageB : Fin n → Quotient (commonBlockOldSetoid true))
    (hf : ∀ i : Fin n,
      imageB i = commonBlockForward (imageA i))
    (hg : ∀ i : Fin n,
      imageA (malformedCycleStep n i) =
        commonBlockBackward (imageB i)) :
    ¬ Function.Injective imageA :=
  malformed_cycle_no_injective_completion
    hn commonBlockForward commonBlockBackward
    commonBlockMixedNamedReturnA imageA imageB hf hg

end CCO.UnaryTermsReturn
