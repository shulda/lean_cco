import CCO.GuardedTwoRoot.JoinedClosedImage
import CCO.GuardedTwoRoot.SourceExactMenu

/-! Exact bounded LOCAL source gate. No premise quantifies over arbitrary
larger irreducible substructures. Actual unary-admissibility gives the
selected pair support its source bound; the complete-pattern test is
requested only for that one actual support and only at that bound.
Common survival, exactness and complete closed-image reflection follow
from the chosen actual factor, not from a global hidden completion. -/

universe u v w r z
namespace CCO.GuardedTwoRoot
open CCO.ParityHasse.Original CCO.TransitionClosure CCO.UnaryTermsReturn
open CCO.TypedOrbitFrames CCO.UnaryFreshFrames CCO.HiddenSAPReadings
noncomputable section
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
local notation "Lang" => originalCompletedLanguage S H sap nr2
local notation "Hidden" => originalCompletedStructure S H sap nr2
local notation "Target" => originalPartialTarget S H sap nr2

/-- The actual original target budget, for ANY genuine represented
hidden generator, including orphans; partial domains add no vertex. -/
theorem actual_partial_singleton_budget (y : OriginalCompletedNamedCarrier S H) :
    ((Target).closureAt y).Finite ∧ Nat.card ((Target).closureAt y) ≤
      originalSourceUniformNormalCodeBudget S H := by
  have hClosure : (Target).closureAt y = (Hidden).closureAt y :=
    partialTarget_closure (Hidden) {y}
  constructor
  · rw [hClosure]
    exact original_completed_all_singleton_closures_finite S H sap nr2 y
  · rw [hClosure,original_completed_structure_closureAt_eq]
    exact original_completed_any_generator_uniform S H sap nr2 y

/-- Full actual singleton diagrams, rather than arbitrary finite unary
syntax, give the bound on THIS selected old two-generated source support. -/
theorem actual_pair_support_bound
    {P : Type z} [Finite P]
    (F : CCO.UnarySupport.Structure (originalPartialSignature S H sap nr2) P)
    (hUnary : UnaryAdmissible F (Target)) (b c : P) :
    Nat.card (F.closure {b,c}) ≤ 2 * originalSourceUniformNormalCodeBudget S H :=
  pair_support_bound hUnary (actual_partial_singleton_budget S H sap nr2) b c

/-- The bounded complete-pattern test for precisely the old endpoint
support being used. This does NOT request tests on other source supports
or on any irreducible with more than 2m_typ vertices. -/
def BoundedPairTest
    {P : Type z}
    (F : CCO.UnarySupport.Structure (originalPartialSignature S H sap nr2) P)
    (b c : P) : Prop :=
  (F.closureStructure {b,c}).Irreducible →
  Nat.card (F.closure {b,c}) ≤ 2 * originalSourceUniformNormalCodeBudget S H →
  Nonempty (CCO.UnarySupport.Structure.Embedding (F.closureStructure {b,c}) (Target))

/-- Exact A03/A04 source instance: derive the actual old support bound,
apply ONLY its bounded complete-pattern test, and then construct one
common fine survivor for ALL comparisons in that ONE completed factor. -/
theorem bounded_pair_source_factor
    {P : Type z} [Finite P]
    (F : CCO.UnarySupport.Structure (originalPartialSignature S H sap nr2) P)
    (hUnary : UnaryAdmissible F (Target)) (b c : P) (hbc : b ≠ c)
    (hirr : (F.closureStructure {b,c}).Irreducible)
    (hTest : BoundedPairTest S H sap nr2 F b c) :
    let b' : F.closure {b,c} := ⟨b,F.subset_closure _ (by simp)⟩
    let c' : F.closure {b,c} := ⟨c,F.subset_closure _ (by simp)⟩
    Nat.card (F.closure {b,c}) ≤ 2 * originalSourceUniformNormalCodeBudget S H ∧
    ∃ e : CCO.UnarySupport.Structure.Embedding (F.closureStructure {b,c}) (Target),
      (pairMenu S H sap nr2 (factorRecords S H sap nr2
        ⟨e.point b',e.sort_eq b'⟩ ⟨e.point c',e.sort_eq c'⟩)).Nonempty := by
  dsimp only
  have hBound := actual_pair_support_bound S H sap nr2 F hUnary b c
  obtain ⟨e⟩ := hTest hirr hBound
  let b' : F.closure {b,c} := ⟨b,F.subset_closure _ (by simp)⟩
  let c' : F.closure {b,c} := ⟨c,F.subset_closure _ (by simp)⟩
  have hRoots : b' ≠ c' := fun he => hbc (congrArg Subtype.val he)
  obtain ⟨x,y,a,_,ha⟩ := one_factor_all_comparisons S H sap nr2
    (F.closureStructure {b,c}) e b' c' hRoots
  exact ⟨hBound,e,a,ha⟩

/-- ANY surviving atom of the selected bounded support reconstructs
its WHOLE induced closed diagram, with literal canonical root values.
The source premise is only its actual bounded local test, never global
JoinedAdmissible or completion of the surrounding partial structure. -/
theorem bounded_pair_every_atom_complete_image
    {P : Type z} [Finite P]
    (F : CCO.UnarySupport.Structure (originalPartialSignature S H sap nr2) P)
    (hUnary : UnaryAdmissible F (Target)) (b c : P) (hbc : b ≠ c)
    (hirr : (F.closureStructure {b,c}).Irreducible)
    (hTest : BoundedPairTest S H sap nr2 F b c) :
    let b' : F.closure {b,c} := ⟨b,F.subset_closure _ (by simp)⟩
    let c' : F.closure {b,c} := ⟨c,F.subset_closure _ (by simp)⟩
    Nat.card (F.closure {b,c}) ≤ 2 * originalSourceUniformNormalCodeBudget S H ∧
    ∃ e : CCO.UnarySupport.Structure.Embedding (F.closureStructure {b,c}) (Target),
      let q : (Hidden).Carrier (F.sort b) := ⟨e.point b',e.sort_eq b'⟩
      let s : (Hidden).Carrier (F.sort c) := ⟨e.point c',e.sort_eq c'⟩
      (pairMenu S H sap nr2 (factorRecords S H sap nr2 q s)).Nonempty ∧
      ∀ a ∈ pairMenu S H sap nr2 (factorRecords S H sap nr2 q s),
        ∀ (x : X (F.sort b).down.1) (y : X (F.sort c).down.1), S.atomRel a x y →
        ∃ f : CCO.UnarySupport.Structure.Embedding (F.closureStructure {b,c}) (Target),
          f.point b' = (Hidden).eval (rootBaseTerm S H sap nr2 (F.sort b))
            (.inl ⟨(F.sort b).down.1,x⟩) ∧
          f.point c' = (Hidden).eval (rootBaseTerm S H sap nr2 (F.sort c))
            (.inl ⟨(F.sort c).down.1,y⟩) ∧
          Set.range f.point = (Target).closure
            {(Hidden).eval (rootBaseTerm S H sap nr2 (F.sort b)) (.inl ⟨(F.sort b).down.1,x⟩),
             (Hidden).eval (rootBaseTerm S H sap nr2 (F.sort c)) (.inl ⟨(F.sort c).down.1,y⟩)} ∧
          Nonempty (CCO.UnarySupport.Structure.DiagramIso (F.closureStructure {b,c})
            ((Target).induce (Set.range f.point) (SourceSupport.embedding_range_closed f))) := by
  dsimp only
  obtain ⟨hBound,e,hMenu⟩ := bounded_pair_source_factor S H sap nr2 F hUnary b c hbc hirr hTest
  refine ⟨hBound,e,hMenu,?_⟩
  intro a ha x y hxy
  let b' : F.closure {b,c} := ⟨b,F.subset_closure _ (by simp)⟩
  let c' : F.closure {b,c} := ⟨c,F.subset_closure _ (by simp)⟩
  obtain ⟨f,hb,hc,_,hIso⟩ := one_factor_complete_closed_image S H sap nr2
    (F.closureStructure {b,c}) e b' c' ha hxy
  have hRange := embedding_two_generated_range (Hidden) (F.closureStructure {b,c})
    f b' c' (pair_support_generated S H sap nr2 F b c)
  rw [hb,hc] at hRange
  exact ⟨f,hb,hc,hRange,hIso⟩

end
end CCO.GuardedTwoRoot
