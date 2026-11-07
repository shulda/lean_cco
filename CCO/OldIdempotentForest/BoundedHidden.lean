import CCO.OldIdempotentForest.CycleReconstructionSource
import CCO.OldIdempotentForest.SourceBounds

/-! The binary source16 bounded-obstruction theorem. Both branches select
an induced, unary-closed subset of the ACTUAL original source. The long
branch derives its no-Hom contradiction from the specified original cycle,
its computed ordered supported sides, the received forest and the one-base
original-word reconstruction. No reconstruction or completion provider is
an additional hypothesis. -/

universe u v w r z
namespace CCO.OldIdempotentForest
open CCO.GuardedOldSeams CCO.GuardedTwoRoot
open CCO.TypedOrbitFrames CCO.UnaryFreshFrames CCO.HiddenSAPReadings
open CCO.UnarySupport CCO.UnarySupport.Structure
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
variable (hCover : ∀ i, OriginalAllFullCoversInfinite S (i := i))
variable (cco : SemanticCCO.{u,v,max u v,w} S)
variable {P : Type z} [Finite P]
variable (F : CCO.UnarySupport.Structure (originalPartialSignature S H sap nr2) P)

include hCover cco

/-- Every noncompletable unary-admissible finite binary hidden source has
an ACTUAL noncompletable induced closed OLD support within the fixed budget.
The local joined tests and the retained-support no-Hom statement are proved
inside the argument, rather than imposed as extra source hypotheses. -/
theorem typed_bounded_hidden
    (hUnary : UnaryAdmissible F (originalPartialTarget S H sap nr2))
    (hNo : ¬ FiniteHiddenCompletion S H sap nr2 F) :
    ∃ (D : Set P) (hD : F.IsClosed D), Nat.card D ≤ typedObstructionBudget S H ∧
      ¬ FiniteHiddenCompletion S H sap nr2 (F.induce D hD) := by
  classical
  by_cases tests : BoundedJoinedPairTests S H sap nr2 F
  · obtain ⟨original,hBad⟩ := hidden_noncompletion_has_specified_bad_cycle S H sap nr2 F
      hUnary tests hCover (CCO.semanticCCO_change_universe S cco) hNo
    obtain ⟨data⟩ := supported_specified_cycle_exists S H sap nr2 F hUnary tests hCover original
    obtain ⟨R⟩ := sourcePrunedForest_exists S H sap nr2 F data.chain data.positive
    apply source_obstruction_of_pruned_no_hom S H sap nr2 F data.chain R hUnary
    rintro ⟨f⟩
    obtain ⟨out⟩ := source_reconstruction_requests_of_hom S H sap nr2 F data.chain R
      hUnary cco data.root_injective data.anchor f
    exact hBad (data.reconstruct_cycle_hom R out)
  · exact source_obstruction_of_failed_tests S H sap nr2 F hUnary tests

/-- The same language constant works for EVERY finite input carrier in
the chosen universe. In particular it is independent of input size, the
original bad-cycle length and the chosen old-root representatives. -/
theorem typed_bounded_hidden_uniform :
    ∃ N : ℕ, ∀ {P : Type z} [Finite P]
      (F : CCO.UnarySupport.Structure (originalPartialSignature S H sap nr2) P),
      UnaryAdmissible F (originalPartialTarget S H sap nr2) →
      ¬ FiniteHiddenCompletion S H sap nr2 F →
      ∃ (D : Set P) (hD : F.IsClosed D), Nat.card D ≤ N ∧
        ¬ FiniteHiddenCompletion S H sap nr2 (F.induce D hD) := by
  exact ⟨typedObstructionBudget S H, fun F hUnary hNo =>
    typed_bounded_hidden S H sap nr2 hCover cco F hUnary hNo⟩

end CCO.OldIdempotentForest
