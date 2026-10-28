import CCO.SIR.Positive.Direct.CCO
import CCO.SIR.Positive.Direct.Consumers
import CCO.SIR.Positive.Direct.PrescribedMap

/-! The concrete original e,d,n source discharges every provider of the
relative-index-two example. Its direct SIR proof never uses HS or NR2. -/
namespace CCO.SIR.Positive.Direct

/-- C25: the actual countable original one-sort source is homogeneous,
SAP and semantic CCO, with infinite lower fibres and an actual relative
index two, and its real finite sets carry the DIRECT pointwise SIR. -/
theorem positive_relative_two_sheet :
    Countable Point ∧ HomogeneousSource source Aut ∧ AgeSAP source ∧
      SemanticCCO.{0,0,0,0} source ∧
      StationaryIndependence (G := Aut) Independent ∧
      Selectors.RelativeIndexTwo sheetSetoid parentSetoid ∧
      (∀ a, Infinite {x // sheetSetoid a x}) ∧
      (∀ a, ParityHasse.Original.relativeIndex sheetSetoid parentSetoid a = 2) ∧
      ¬ Selectors.OriginalNR2 source :=
  ⟨inferInstance,homogeneous,strongAmalgamation,semanticCCO,stationaryIndependence,
    relativeIndexTwo,infinite_sheet,actual_relative_index,violates_originalNR2⟩

/-- The entire full invariant lattice and all proper GLOBAL indices are
computed in the old language; no quotient names or Hasse provider are inputs. -/
theorem original_full_equivalence_control (R : Setoid Point)
    (hR : Selectors.InvariantSetoid (X := fun _ : Unit => Point) (G := Aut) (i := ()) R) :
    (R = ⊥ ∨ R = sheetSetoid ∨ R = parentSetoid ∨ R = ⊤) ∧
      (R ≠ ⊤ → Infinite (Quotient R)) :=
  ⟨full_invariant_lattice R hR,infinite_global_quotient R hR⟩

/-- A genuine downstream completion on arbitrary finite formal carriers.
No HS, NR2 or completion interface is a premise. -/
theorem real_strong_completion {V : Type*} (D : PartialDiagram source V)
    (hcycles : ∀ C : SimpleCycle D, CycleHom C) :
    ∃ f : DiagramHom D, f.IsInjective :=
  injective_complete_of_cycles D hcycles

end CCO.SIR.Positive.Direct
