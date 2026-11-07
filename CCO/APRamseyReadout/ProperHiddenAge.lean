import CCO.APRamseyReadout.ActualSource
import CCO.TerminalHiddenHN.RamseyBridge
import CCO.APRamseyReadout.ResetCodecs

/-! The whole B059 age and its ALL-proper-sort restriction on the SAME
actual terminal clone source. No chart-generated or no-orphan condition
is imposed. Every named unary output is proper, so this restriction
retains all function domains, values and induced relation tests. -/

universe u v w z
namespace CCO.APRamseyReadout
open CCO.CloneTupleGeometry CCO.UnaryTermsReturn CCO.TypedOrbitFrames
noncomputable section
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal)

/-- In particular no named quotient-to-real return is introduced. -/
theorem properSort_output (F : (Lang B ht).Func) :
    ProperSort B ht ((Lang B ht).output F) := by
  rcases F with ⟨F⟩
  cases F with
  | inl F => rcases F with ⟨i,D⟩; trivial
  | inr F =>
    cases F with
    | inl F => rcases F with ⟨i,⟨⟨D,E⟩,hDE⟩⟩; trivial
    | inr F => rcases F with ⟨i,j,a⟩; trivial

theorem properSort_closed :
    ∀ F : (Lang B ht).Func,
      ProperSort B ht ((Lang B ht).input F) → ProperSort B ht ((Lang B ht).output F) :=
  fun F _ => properSort_output B ht F

/-- Every actual partial source retains exactly the same prescribed
unary output sort. Its proper part is genuinely closed, not a projection
that drops values whose names were absent from the chosen chart. -/
theorem proper_set_closed {V : Type z}
    (C : CCO.UnarySupport.Structure (Sig B ht) V) :
    C.IsClosed {x | ProperSort B ht (C.sort x)} := by
  intro F x _ y hy
  have hsort := (C.func_sorted F x y hy).2
  change ProperSort B ht (C.sort y)
  rw [hsort]
  exact properSort_output B ht F

/-- The full actual unordered proper age, on arbitrary carrier copies. -/
def ProperAge {V : Type z} (C : CCO.UnarySupport.Structure (Sig B ht) V) : Prop :=
  ActualAge B ht C ∧ ∀ x, ProperSort B ht (C.sort x)

theorem proper_restriction_mem {V : Type z}
    {C : CCO.UnarySupport.Structure (Sig B ht) V} (hC : ActualAge B ht C) :
    ProperAge B ht (C.induce {x | ProperSort B ht (C.sort x)} (proper_set_closed B ht C)) := by
  refine ⟨TerminalHiddenHN.actualAge_induce _ _ _ _ hC _ _,?_⟩
  exact fun x => x.property

/-- Strict B059 C30 on the terminal CLONE source, before real readout. -/
theorem whole_age_sap :
    CCO.UnaryHN.Raw.FiniteHereditarySAP (ActualAge.{u,v,w,z} B ht) := by
  letI (i : B.Sorts) : Countable (CloneSAP.Carrier B.Point i) := clone_countable B i
  exact TerminalHiddenHN.actual_hidden_age_sap
    (cloneSource B) (cloneHomogeneous B) (cloneSAP B) (fullCovers B ht) (cloneCCO B)

/-- Strict B059 C36, already translated to the literal full-code
language, with ALL global orders on EVERY actual hidden member. -/
theorem whole_ordered_ramsey :
    CCO.FullCode.HasHiddenRamsey (OrderedAge.{u,v,w,z} B ht) := by
  letI (i : B.Sorts) : Countable (CloneSAP.Carrier B.Point i) := clone_countable B i
  exact TerminalHiddenHN.actual_hidden_fullcode_ramsey
    (cloneSource B) (cloneHomogeneous B) (cloneSAP B) (fullCovers B ht) (cloneCCO B)

theorem whole_ordered_of_embedding
    {A D : CCO.FullCode.FiniteHidden.{max u v w,z}
      (TerminalHiddenHN.orderedLanguage (Sig B ht)
        (TerminalHiddenHN.sig_binary (cloneSource B) (cloneHomogeneous B)
          (cloneSAP B) (fullCovers B ht)))}
    (hD : OrderedAge B ht D) (e : CCO.FullCode.Structure.Embedding A.model D.model) :
    OrderedAge B ht A :=
  TerminalHiddenHN.orderedActualAge_of_embedding _ _ _ _ hD e

theorem whole_ordered_hereditary : CCO.FullCode.HereditaryHidden (OrderedAge.{u,v,w,z} B ht) :=
  TerminalHiddenHN.orderedActualAge_hereditary _ _ _ _

/-- D01 includes all proper coordinates, whether or not a root happens
to generate them. Deleted real sorts are empty, with the language retained. -/
def ProperOrderedAge := fun D => OrderedAge.{u,v,w,z} B ht D ∧
  ∀ x, ProperSort B ht (D.model.sort x)

theorem proper_ordered_of_embedding
    {A D : CCO.FullCode.FiniteHidden.{max u v w,z}
      (TerminalHiddenHN.orderedLanguage (Sig B ht)
        (TerminalHiddenHN.sig_binary (cloneSource B) (cloneHomogeneous B)
          (cloneSAP B) (fullCovers B ht)))}
    (hD : ProperOrderedAge B ht D) (e : CCO.FullCode.Structure.Embedding A.model D.model) :
    ProperOrderedAge B ht A := by
  refine ⟨whole_ordered_of_embedding B ht hD.1 e,?_⟩
  intro x
  rw [← e.sort_eq x]
  exact hD.2 _

/-- All-input term-function normal forms remain valid at every orphan
proper input of every actual ordered member. No Ramsey premise is used
in this normalization statement. -/
theorem proper_ordered_normal (D) (hD : ProperOrderedAge.{u,v,w,z} B ht D) :
    (TerminalHiddenHN.orderedNormalForms (cloneSource B) (cloneHomogeneous B)
      (cloneSAP B) (fullCovers B ht)).Valid D.model :=
  TerminalHiddenHN.orderedActualAge_normal _ _ _ _ D hD.1

/-- C20: apply the accepted full-language B036 restriction theorem to
the actual B059 whole-age Ramsey witness, keeping every proper sort. -/
theorem proper_ordered_ramsey :
    CCO.FullCode.HasHiddenRamsey (ProperOrderedAge.{u,v,w,z} B ht) := by
  let L := TerminalHiddenHN.orderedLanguage (Sig B ht)
    (TerminalHiddenHN.sig_binary (cloneSource B) (cloneHomogeneous B)
      (cloneSAP B) (fullCovers B ht))
  let I : Set L.Sorts := fun s => ProperSort B ht s
  have hI : ∀ F : L.Func, L.input F ∈ I → L.output F ∈ I := by
    intro F _
    exact properSort_output B ht F
  have hK : FullHereditary L (OrderedAge.{u,v,w,z} B ht) := by
    intro A D hD e
    exact whole_ordered_of_embedding B ht hD e
  exact fullCode_sort_restriction_ramsey L I hI hK (whole_ordered_ramsey B ht)

theorem proper_ordered_hereditary :
    CCO.FullCode.HereditaryHidden (ProperOrderedAge.{u,v,w,z} B ht) := by
  intro D hD T hT
  exact proper_ordered_of_embedding B ht hD (D.model.inclusion T hT)

end
end CCO.APRamseyReadout
