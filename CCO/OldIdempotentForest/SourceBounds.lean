import CCO.OldIdempotentForest.ForestAdapterSource
import CCO.RawExact.DiagramReindex

/-! Fixed original-language obstruction constants and the two exact
OLD-support branches. The long-branch no-Hom premise is discharged by
the actual cycle reconstruction in the final source consumer. -/

universe u v w r z
namespace CCO.OldIdempotentForest
open CCO.UnarySupport CCO.UnarySupport.Structure
open CCO.ParityHasse.Original CCO.TransitionClosure CCO.UnaryTermsReturn
open CCO.TypedOrbitFrames CCO.UnaryFreshFrames CCO.HiddenSAPReadings
open CCO.GuardedTwoRoot CCO.GuardedOldSeams
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)

/-- Depends only on the original source language/profile families,
never the input size, the original cycle length or representative choices.
Actual bad cycles inside one seeded theta are already excluded. -/
noncomputable def typedObstructionBudget : ℕ :=
  max (2 * originalSourceUniformNormalCodeBudget S H)
    (originalSourceUniformNormalCodeBudget S H *
      (2 ^ (3 * Nat.card (TypedProfileState S)+3)+4))

variable {P : Type z} [Finite P]
variable (F : CCO.UnarySupport.Structure (originalPartialSignature S H sap nr2) P)

/-- The malformed local branch is an ACTUAL irreducible old closure
with its complete induced diagram and derived 2m bound. -/
theorem source_obstruction_of_failed_tests
    (hUnary : UnaryAdmissible F (originalPartialTarget S H sap nr2))
    (hTests : ¬ BoundedJoinedPairTests S H sap nr2 F) :
    ∃ (D : Set P) (hD : F.IsClosed D), Nat.card D ≤ typedObstructionBudget S H ∧
      ¬ FiniteHiddenCompletion S H sap nr2 (F.induce D hD) := by
  obtain ⟨D,hD,hBound,hNo⟩ := failed_bounded_pair_has_small_obstruction S H sap nr2 F hUnary hTests
  exact ⟨D,hD,hBound.trans (Nat.le_max_left _ _),hNo⟩

variable {n : ℕ} (C : SupportedMacroChain S H sap nr2 F n)
variable (R : SourcePrunedForest S H sap nr2 F C)

/-- A genuine hypothetical finite HE completion gives a homomorphism
of precisely the retained old source into the actual original target. -/
theorem pruned_finite_completion_has_hom
    (h : FiniteHiddenCompletion S H sap nr2
      (F.closureStructure (R.oldGenerators : Set P))) :
    Nonempty (Hom (F.closureStructure (R.oldGenerators : Set P))
      (originalPartialTarget S H sap nr2)) := by
  obtain ⟨D,_,hD,f,_⟩ := h
  exact ⟨closedInducedHom hD f⟩

/-- The numerical/induced-source endpoint of the long branch. It does
not replace the concrete reconstruction which proves no Hom exists. -/
theorem source_obstruction_of_pruned_no_hom
    (hUnary : UnaryAdmissible F (originalPartialTarget S H sap nr2))
    (hNo : ¬ Nonempty (Hom (F.closureStructure (R.oldGenerators : Set P))
      (originalPartialTarget S H sap nr2))) :
    ∃ (D : Set P) (hD : F.IsClosed D), Nat.card D ≤ typedObstructionBudget S H ∧
      ¬ FiniteHiddenCompletion S H sap nr2 (F.induce D hD) := by
  refine ⟨F.closure (R.oldGenerators : Set P),F.isClosed_closure _,
    (R.old_anchor_bound hUnary).trans (Nat.le_max_right _ _),?_⟩
  intro h
  exact hNo (pruned_finite_completion_has_hom S H sap nr2 F C R h)

end CCO.OldIdempotentForest
