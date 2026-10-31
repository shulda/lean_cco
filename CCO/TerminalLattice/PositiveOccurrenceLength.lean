import CCO.TerminalLattice.OptionalPositiveNetwork
import CCO.RawExact.QuotientExpansionCycleRealization

/-!
# B050 C27: all actual private word occurrences have POSITIVE old length

A genuinely specified old private path is a nonempty ORIGINAL positive
atom word. A missing edge has an empty presentation and therefore
NO occurrence. This discharges the actual B002 `hPositive` input
for an arbitrary cycle of the ONE constructed OLD diagram.

This module also packages the accepted source B002 step: once the
actual marked roots of one cycle have been assigned old real points
satisfying EVERY used original menu, one actual cycle homomorphism
follows from the real typed private paths. Such a marked-root
assignment is still the explicit open C27/C32 combinatorial task.
-/

universe u v w t

namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ j : ι, MulAction G (X j)]

/-- Every original typed positive word has a genuine first diversity
edge in its RAW encoding. No logical identity letter is counted. -/
theorem oldPositiveWord_diversityLength_pos {i j : ι}
    (w : PositiveWord S i j) :
    0 < CCO.RawExact.diversityLength S (PositiveWord.toRawWord S w) := by
  induction w with
  | single a =>
      simp only [PositiveWord.toRawWord,
        CCO.RawExact.diversityLength_atom,
        CCO.RawExact.diversityLength_nil]
      omega
  | cons a rest ih =>
      simp only [PositiveWord.toRawWord,
        CCO.RawExact.diversityLength_atom]
      omega

/-- The original B002 private expansion of ONE optional-positive-word
presentation contains no zero-diversity occurrence. The truly
missing edges contribute NO occurrence, not zero-length words. -/
theorem oldOptionalPositive_occurrence_length_pos
    {i : ι} {n : Nat}
    (words : CCO.RawExact.QuotientExpansion.Edge n →
      Option (PositiveWord S i i))
    (o : CCO.RawExact.QuotientExpansion.Occurrence S
      (fun _ : Fin n => i) (oldOptionalPositivePresentations S words)) :
    0 < CCO.RawExact.diversityLength S
      (CCO.RawExact.QuotientExpansion.word S
        (fun _ : Fin n => i)
        (oldOptionalPositivePresentations S words) o) := by
  let P := oldOptionalPositivePresentations S words
  rcases o with ⟨e,slot⟩
  have hmem :
      CCO.RawExact.QuotientExpansion.word S
        (fun _ : Fin n => i) P ⟨e,slot⟩ ∈ P e :=
    List.get_mem (P e) slot
  cases h : words e with
  | none =>
      have hFalse : False := by
        simpa [P,oldOptionalPositivePresentations,h] using hmem
      exact False.elim hFalse
  | some w =>
      have hw : CCO.RawExact.QuotientExpansion.word S
          (fun _ : Fin n => i) P ⟨e,slot⟩ =
            PositiveWord.toRawWord S w := by
        simpa [P,oldOptionalPositivePresentations,h] using hmem
      rw [hw]
      exact oldPositiveWord_diversityLength_pos S w

/-- Receiving step for source C27/C32: once an actual labelled
marked-cycle root assignment satisfies all used OLD represented
positive words (rather than an abstract quotient), the accepted
B002 path constructor supplies a genuine homomorphism of its ENTIRE
original specified simple cycle with all intermediate named sorts.

The marked-root assignment is explicitly retained as an INPUT:
this theorem does not assume original CCO or manufacture the still
open graph-cycle colouring/realization. -/
theorem oldOptionalPositive_cycleHom_of_marked_assignment
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} {n : Nat}
    (words : CCO.RawExact.QuotientExpansion.Edge n →
      Option (PositiveWord S i i))
    (C : SimpleCycle (oldOptionalPositiveDiagram S H sap words))
    (b : Fin n → X i)
    (hEval : ∀ e,
      CCO.RawExact.QuotientExpansion.CycleUsesEdge S
        (fun _ : Fin n => i)
        (oldOptionalPositivePresentations S words)
        (oldOptionalPositivePresentations_nonempty S H sap words) C e →
      CCO.RawExact.evaluate S
        (oldOptionalPositivePresentations S words e)
        (b (CCO.RawExact.QuotientExpansion.left e))
        (b (CCO.RawExact.QuotientExpansion.right e))) :
    CycleHom C := by
  exact CCO.RawExact.QuotientExpansion.cycleHom_of_marked_edge_realization
    S (fun _ : Fin n => i)
    (oldOptionalPositivePresentations S words)
    (oldOptionalPositivePresentations_nonempty S H sap words)
    C b hEval
    (oldOptionalPositive_occurrence_length_pos S words)

end CCO.TerminalLattice
