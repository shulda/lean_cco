import CCO.GuardedTwoRoot.BoundedSourcePair
import CCO.GuardedTwoRoot.UniformTheta

/-! Actual finite COMPLETE comparison records on the selected OLD
source values. Primitive graph symbols, full named binary labels and
literal equality are counted by the fixed finite signature. Composed
term graphs reduce to equality of actual old term VALUES in the same
closed embedded factor; no bound on term syntax is assumed. -/

universe u v w r z
namespace CCO.GuardedTwoRoot
open CCO.ParityHasse.Original CCO.TransitionClosure CCO.UnaryTermsReturn
open CCO.TypedOrbitFrames CCO.UnaryFreshFrames CCO.HiddenSAPReadings
noncomputable section
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
local notation "Sig" => originalPartialSignature S H sap nr2
local notation "Lang" => originalCompletedLanguage S H sap nr2
local notation "Hidden" => originalCompletedStructure S H sap nr2
local notation "Target" => originalPartialTarget S H sap nr2

abbrev CompleteRecordName := (Sig).Rel ⊕ (Unit ⊕ (Sig).Func)

def completeRecordBudget : ℕ := Nat.card (CompleteRecordName S H sap nr2)

def CompleteRecordHolds {P : Type z}
    (F : CCO.UnarySupport.Structure (Sig) P)
    (record : (P × P) × CompleteRecordName S H sap nr2) : Prop :=
  match record.2 with
  | .inl name => F.rel name (fun k => if k.val = 0 then record.1.1 else record.1.2)
  | .inr (.inl _) => record.1.1 = record.1.2
  | .inr (.inr f) => record.1.2 ∈ F.func f record.1.1

abbrev CompleteSourceRecord {P : Type z}
    (F : CCO.UnarySupport.Structure (Sig) P) :=
  {record : (P × P) × CompleteRecordName S H sap nr2 // CompleteRecordHolds S H sap nr2 F record}

/-- C23's source-derived finite count, with u=m_typ and R the ACTUAL
fixed-language equality/binary/primitive-graph name budget. -/
theorem actual_complete_record_bound
    {P : Type z} [Finite P]
    (F : CCO.UnarySupport.Structure (Sig) P)
    (hUnary : UnaryAdmissible F (Target)) (b c : P) :
    Nat.card (CompleteSourceRecord S H sap nr2 (F.closureStructure {b,c})) ≤
      comparisonBound (originalSourceUniformNormalCodeBudget S H)
        (completeRecordBudget S H sap nr2) := by
  have hValues := actual_pair_support_bound S H sap nr2 F hUnary b c
  have hPool := Nat.mul_le_mul_right (completeRecordBudget S H sap nr2)
    (Nat.mul_le_mul hValues hValues)
  apply (Nat.card_le_card_of_injective
    (Subtype.val : CompleteSourceRecord S H sap nr2 (F.closureStructure {b,c}) →
      ((F.closure {b,c} × F.closure {b,c}) × CompleteRecordName S H sap nr2))
    Subtype.val_injective).trans
  simpa only [Nat.card_prod,completeRecordBudget,comparisonBound,Nat.pow_two,Nat.mul_comm] using hPool

/-- EVERY composed named term in the actual factor already has one
literal OLD source value. Its graph comparison against any other source
value is exactly their literal equality, with no independent target value. -/
theorem actual_factor_term_graph_value
    {P : Type z}
    (F : CCO.UnarySupport.Structure (Sig) P)
    (e : CCO.UnarySupport.Structure.Embedding F (Target))
    (p : P) {D : (Lang).Sorts} (term : Term Lang (F.sort p) D) (q : P) :
    ∃ value : P, e.point value = (Hidden).eval term (e.point p) ∧
      ((Hidden).eval term (e.point p) = e.point q ↔ value = q) := by
  have hClosed : (Hidden).Closed (Set.range e.point) :=
    (partialTarget_closed_iff (Hidden) _).mp (SourceSupport.embedding_range_closed e)
  obtain ⟨value,hValue⟩ := (Hidden).eval_mem_closed hClosed term (Set.mem_range_self p)
  refine ⟨value,hValue,?_⟩
  constructor
  · intro h
    exact e.injective (hValue.trans h)
  · intro h
    subst q
    exact hValue.symm

end
end CCO.GuardedTwoRoot
