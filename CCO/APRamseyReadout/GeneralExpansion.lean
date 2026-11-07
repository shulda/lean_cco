import CCO.APRamseyReadout.RamseyReadout
import CCO.TerminalHiddenHN.UnaryLift

/-! The general original AP source is first replaced by its constructed
terminal pure-clone endpoint. The actual finite readout expansion there
is then pulled back through the SAME proved reasonable unary reduct of
that safe history. Original SAP, terminal covers, selected-coordinate
providers, real-hull/cofinality premises, and expansion property are not
assumptions of either general source theorem. -/

universe u v w r p
namespace CCO.APRamseyReadout
open CCO.CloneTupleGeometry CCO.TerminalHiddenHN
open CCO.APCharacter.Towers
noncomputable section

/-- A fixed priority of the finite hidden sort SYMBOLS. It is chosen
independently of points, finite objects, and quotient representatives. -/
def defaultReadoutPriority (B : OwnerStage.{u,v,w}) (ht : B.Terminal) :
    LinearOrder (CoordinateLanguage B ht).Sorts := by
  letI : Fintype (CoordinateLanguage B ht).Sorts := Fintype.ofFinite _
  exact LinearOrder.lift' (Fintype.equivFin _) (Fintype.equivFin _).injective

/-- The parameterized terminal witness contains the full finite code
and arbitrary global support orders, for the given fixed meet-K chart. -/
theorem terminal_full_readout_expansion (B : OwnerStage.{u,v,w}) (ht : B.Terminal)
    (F : Charts.{u,v,w,p} B) :
    HasFiniteRelationalRamseyExpansion.{u,v,w,max u v w,max u v} B.source :=
  ⟨actualFullReadoutData B ht F,actualFullReadoutData_reasonable B ht F,
    actual_full_readout_ramsey B ht F⟩

/-- The smaller terminal witness keeps original fine colours and safe
unary labels, adding only within-HIDDEN-target-sort comparisons. -/
theorem terminal_small_readout_expansion (B : OwnerStage.{u,v,w}) (ht : B.Terminal)
    (F : Charts.{u,v,w,p} B) (priority : LinearOrder (CoordinateLanguage B ht).Sorts) :
    HasFiniteRelationalRamseyExpansion.{u,v,w,max u v w,max u v} B.source :=
  ⟨actualSmallReadoutData B ht F priority,
    actualSmallReadoutData_reasonable B ht F priority,
    actual_small_readout_ramsey B ht F priority⟩

section Original
variable {ι : Type u} {X : ι → Type v} (S : CCO.AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i : ι, MulAction G (X i)]

/-- C33/C34: the full readout Ramsey expansion of the ORIGINAL age is
obtained from ordinary AP and the actual finite safe-label history.
Every expansion and every embedding still has its original old carrier. -/
theorem general_ap_full_ramsey_expansion
    (H : CCO.HomogeneousSource S G) (ap : CCO.AgeAP S)
    (cco : CCO.SemanticCCO.{u,v,max u v,w} S)
    (countable : ∀ i, Countable (X i)) (infinite : ∀ i, Infinite (X i)) :
    HasFiniteRelationalRamseyExpansion.{u,v,w,max u v w,max u v w} S := by
  obtain ⟨B,history,ht,_hbound,reduct,unary,hforget⟩ :=
    terminal_clone_source_exists S H ap cco countable infinite
  have hTerminal := terminal_full_readout_expansion B ht (defaultCharts B)
  have hReasonable : Reasonable reduct.forget := by
    rw [← hforget]
    exact unary.reasonable
  exact UnaryLift.hasFiniteRelationalRamseyExpansion_of_unaryReduct
    reduct hReasonable hTerminal

/-- The actual smaller finite language also gives the general AP
Ramsey expansion. Safe unary names survive the SAME unary lift; only
the dispensable hidden codes/comparisons have been removed at the
terminal endpoint, using its proved full embedding equivalence. -/
theorem general_ap_small_ramsey_expansion
    (H : CCO.HomogeneousSource S G) (ap : CCO.AgeAP S)
    (cco : CCO.SemanticCCO.{u,v,max u v,w} S)
    (countable : ∀ i, Countable (X i)) (infinite : ∀ i, Infinite (X i)) :
    HasFiniteRelationalRamseyExpansion.{u,v,w,max u v w,max u v w} S := by
  obtain ⟨B,history,ht,_hbound,reduct,unary,hforget⟩ :=
    terminal_clone_source_exists S H ap cco countable infinite
  have hTerminal := terminal_small_readout_expansion B ht (defaultCharts B)
    (defaultReadoutPriority B ht)
  have hReasonable : Reasonable reduct.forget := by
    rw [← hforget]
    exact unary.reasonable
  exact UnaryLift.hasFiniteRelationalRamseyExpansion_of_unaryReduct
    reduct hReasonable hTerminal

/-- The general AP source export uses the full readout proof, independently
of block normalization. The smaller-language corollary remains a separate
source export with the same original AP hypotheses. -/
theorem general_ap_ramsey_expansion
    (H : CCO.HomogeneousSource S G) (ap : CCO.AgeAP S)
    (cco : CCO.SemanticCCO.{u,v,max u v,w} S)
    (countable : ∀ i, Countable (X i)) (infinite : ∀ i, Infinite (X i)) :
    HasFiniteRelationalRamseyExpansion.{u,v,w,max u v w,max u v w} S :=
  general_ap_full_ramsey_expansion S H ap cco countable infinite

end Original
end
end CCO.APRamseyReadout
