import CCO.CloneTupleGeometry.SelectedMIFamily
import CCO.TerminalHiddenHN.OrderedAge
import Mathlib.SetTheory.Cardinal.Finite

/-! The single actual terminal pure-clone interpretation used by B061.
The terminal owner source is supplied by the proved finite safe history;
no original owner SAP or terminality is assumed. Fixed charts enumerate
symbols once, independently of points, and do not restrict the proper
hidden age to only those selected coordinates. -/

universe u v w p z r
namespace CCO.APRamseyReadout
open CCO.CloneTupleGeometry CCO.CloneTupleGeometry.OwnerStage
noncomputable section

variable (B : OwnerStage.{u,v,w})

abbrev cloneSource := CloneSAP.source B.source
abbrev cloneHomogeneous := CloneSAP.homogeneous B.source B.homogeneous
abbrev cloneSAP := CloneSAP.strong_amalgamation B.source B.ap
abbrev cloneCCO := CloneSAP.CCO.cco_forward B.source B.cco

/-- Every FULL cover, including a Top cover, has infinite relative index
in the same actual safe endpoint. -/
theorem fullCovers (ht : B.Terminal) (i : B.Sorts) :
    TypedOrbitFrames.OriginalAllFullCoversInfinite (cloneSource B) (i := i) :=
  fun E F hEF x => B.terminal_interval_infinite ht E F hEF.lt x

abbrev HF := TerminalHiddenHN.HF (cloneSource B) (cloneHomogeneous B)
abbrev Lang (ht : B.Terminal) :=
  TerminalHiddenHN.Lang (cloneSource B) (cloneHomogeneous B) (cloneSAP B) (fullCovers B ht)
abbrev Values := TerminalHiddenHN.Values (cloneSource B) (cloneHomogeneous B)
abbrev Hidden (ht : B.Terminal) :=
  TerminalHiddenHN.Hidden (cloneSource B) (cloneHomogeneous B) (cloneSAP B) (fullCovers B ht)
abbrev Sig (ht : B.Terminal) :=
  TerminalHiddenHN.Sig (cloneSource B) (cloneHomogeneous B) (cloneSAP B) (fullCovers B ht)
abbrev Target (ht : B.Terminal) :=
  TerminalHiddenHN.Target (cloneSource B) (cloneHomogeneous B) (cloneSAP B) (fullCovers B ht)
abbrev ActualAge (ht : B.Terminal) {V : Type z}
    (C : CCO.UnarySupport.Structure (Sig B ht) V) : Prop :=
  TerminalHiddenHN.ActualAge.{u,v,w,max u v,z}
    (cloneSource B) (cloneHomogeneous B) (cloneSAP B) (fullCovers B ht) C
abbrev OrderedAge (ht : B.Terminal) :=
  TerminalHiddenHN.OrderedActualAge.{u,v,w,max u v,z}
    (cloneSource B) (cloneHomogeneous B) (cloneSAP B) (fullCovers B ht)

/-- This selects ALL actual proper named quotient sorts. Intermediate
term values need not belong to the fixed visible chart. -/
def ProperSort (ht : B.Terminal) (s : (Lang B ht).Sorts) : Prop :=
  match s.down.2 with
  | .inl _ => False
  | .inr _ => True

/-- Clone countability is inherited from the actual owner source. -/
theorem clone_countable (i : B.Sorts) : Countable (CloneSAP.Carrier B.Point i) := by
  letI := B.countable
  infer_instance

/-- A chart is any once-fixed finite DISTINCT proper-MI family with
literal FULL meet K. Choosing all proper MIs is only one allowed instance. -/
abbrev Charts := ∀ i : B.Sorts, SelectedMIFamily.{u,v,w,p} B i

variable {B} (F : Charts.{u,v,w,p} B)

def chartArity (i : B.Sorts) : ℕ := Nat.card (F i).Index

theorem chartArity_pos (i : B.Sorts) : 0 < chartArity F i :=
  Nat.card_pos_iff.mpr ⟨(F i).nonemptyIndex,inferInstance⟩

/-- The enumeration is of a finite symbol family, never of tuples or
of quotient representatives depending on an input point. -/
def chartEnumeration (i : B.Sorts) : (F i).Index ≃ Fin (chartArity F i) :=
  Nat.equivFinOfCardPos (ne_of_gt (chartArity_pos F i))

def chartSymbol (i : B.Sorts) (k : Fin (chartArity F i)) :
    FullCloneProperMI B.source i :=
  (F i).symbol ((chartEnumeration F i).symm k)

theorem chartSymbol_injective (i : B.Sorts) : Function.Injective (chartSymbol F i) :=
  (F i).symbol_injective.comp (chartEnumeration F i).symm.injective

theorem chartSymbol_kernel_le (i : B.Sorts) (k : Fin (chartArity F i)) :
    fullCloneKernel B.source i ≤ (chartSymbol F i k).val :=
  (F i).kernel_le _

variable (B)

/-- The main source application may choose every proper MI symbol;
the parameterized template results still allow arbitrary fixed charts. -/
def defaultCharts : Charts.{u,v,w,v} B :=
  fun i => SelectedMIFamily.all B i

section Original
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]

/-- Original AP, rather than SAP, constructs the NEW actual safe owner
endpoint. The retained unary transition is the SAME reduct functor along
the actual finite history, not an independently supplied label provider. -/
theorem terminal_clone_source_exists
    (H : HomogeneousSource S G) (ap : AgeAP S)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    (countable : ∀ i, Countable (X i)) (infinite : ∀ i, Infinite (X i)) :
    ∃ B : OwnerStage.{u,v,w},
      ∃ history : APCharacter.Towers.History OwnerStage.Next
        (initialOwnerStage S H ap cco countable infinite) B,
        B.Terminal ∧
        history.length + B.potential ≤ (initialOwnerStage S H ap cco countable infinite).potential ∧
        ∃ reduct : APCharacter.Towers.UnaryReduct S B.source,
          ∃ unary : APCharacter.Towers.UnaryTransition
            (initialOwnerStage S H ap cco countable infinite).finiteAge B.finiteAge,
            unary.forget = reduct.forget := by
  obtain ⟨D,history,ht,hbound,reduct,unary,hforget,_⟩ :=
    CloneTupleGeometry.ramsey_clone_stability S H ap cco countable infinite
  exact ⟨D,history,ht,hbound,reduct,unary,hforget⟩

end Original
end
end CCO.APRamseyReadout
