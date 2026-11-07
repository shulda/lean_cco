import CCO.TerminalHiddenHN.CompletionBridge
import CCO.OldIdempotentForest.BoundedHidden
import Mathlib.Data.Set.Card

/-! Bind the accepted geometric bound to the EXACT HN direct gate.
The returned actual OLD closed set is converted to the SAME Finset;
neither its closure nor its cardinality is enlarged. Unary admissibility
comes from actual completed singleton membership, never mere totality. -/

universe u v w r z
namespace CCO.TerminalHiddenHN
open CCO.UnarySupport CCO.UnarySupport.Structure
open CCO.GuardedTwoRoot CCO.GuardedOldSeams
open CCO.HiddenSAPReadings CCO.TypedOrbitFrames CCO.UnaryTermsReturn
noncomputable section
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G)

/-- Exactly the accepted source16 language bound, viewed as an integer
for the HN interface. It is independent of every finite input carrier. -/
def obstructionBound : ℤ := (CCO.OldIdempotentForest.typedObstructionBudget S (HF S H) : ℤ)

def obstructionCutoff : ℕ := CCO.UnaryHN.Native.obstructionCutoff (obstructionBound S H)

theorem obstructionCutoff_eq : obstructionCutoff S H =
    max 1 (CCO.OldIdempotentForest.typedObstructionBudget S (HF S H)) := by
  unfold obstructionCutoff CCO.UnaryHN.Native.obstructionCutoff obstructionBound
  omega

variable (sap : AgeSAP S) (hCover : ∀ i, OriginalAllFullCoversInfinite S (i := i))
variable (cco : SemanticCCO.{u,v,max u v,w} S)

include cco in
/-- This is a source-produced witness in the actual HN carrier, with
the exact original closed induced diagram and the unchanged integer bound. -/
theorem actual_bounded_obstruction_finset {P : Type z} [Finite P]
    (C : Structure (Sig S H sap hCover) P)
    (hUnary : UnaryAdmissible C (Target S H sap hCover))
    (hNo : ¬ CCO.UnaryHN.Raw.HasCompletion (ActualAge S H sap hCover) C) :
    ∃ (B : Finset P) (hB : C.IsClosed (B : Set P)),
      (B.card : ℤ) ≤ obstructionBound S H ∧
        ¬ CCO.UnaryHN.Raw.HasCompletion (ActualAge S H sap hCover) (C.induce (B : Set P) hB) := by
  classical
  have hNoActual : ¬ FiniteHiddenCompletion S (HF S H) sap (NR2 S hCover) C :=
    fun h => hNo ((finiteHiddenCompletion_iff_rawHasCompletion S H sap hCover C).mp h)
  obtain ⟨D,hD,hCard,hBad⟩ := CCO.OldIdempotentForest.typed_bounded_hidden
    S (HF S H) sap (NR2 S hCover) hCover cco C hUnary hNoActual
  let B := D.toFinite.toFinset
  have hSet : (B : Set P) = D := Set.Finite.coe_toFinset _
  have hB : C.IsClosed (B : Set P) := by simpa only [hSet] using hD
  have hCardB : B.card ≤ CCO.OldIdempotentForest.typedObstructionBudget S (HF S H) := by
    rw [← Set.ncard_eq_toFinset_card D D.toFinite]
    exact hCard
  have transfer : ∀ (E : Set P) (hE : C.IsClosed E), E = D →
      ¬ FiniteHiddenCompletion S (HF S H) sap (NR2 S hCover) (C.induce E hE) := by
    intro E hE he
    subst E
    exact hBad
  have hBadB := transfer (B : Set P) hB hSet
  refine ⟨B,hB,Int.ofNat_le.mpr hCardB,?_⟩
  intro hSmall
  exact hBadB ((finiteHiddenCompletion_iff_rawHasCompletion S H sap hCover
    (C.induce (B : Set P) hB)).mpr hSmall)

include cco in
/-- ALL mathematical hypotheses of the HN direct obstruction input are
discharged for this actual age. Its domain is exactly actual completed
one-generated diagrams, including all their partial-domain information. -/
theorem actual_directObstruction :
    CCO.UnaryHN.Raw.DirectObstruction (ActualAge S H sap hCover) (obstructionBound S H) := by
  intro P hP C hOne hNo
  exact actual_bounded_obstruction_finset S H sap hCover cco C
    (unaryAdmissible_of_oneGeneratedDomain S H sap hCover C hOne) hNo

end
end CCO.TerminalHiddenHN
