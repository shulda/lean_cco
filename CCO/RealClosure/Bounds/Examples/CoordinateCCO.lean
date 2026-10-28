import CCO.RealClosure.Bounds.Examples.Coordinate
import CCO.RealClosure.Bounds.Examples.CycleConsistency
import CCO.StrongExact.AgeAP

/-! Infinite-source AP and semantic CCO, rather than finite snapshot checks.
Every coordinate receives a natural label for its specified equality classes;
a failed inequality would create an actual bad specified simple cycle. -/
universe u z
namespace CCO.RealClosure.Bounds.Examples.Coordinate
variable (I : Type u) [Fintype I] [DecidableEq I]

noncomputable def readEq (i : I) : CycleConsistency.Reader (source I) :=
  fun a => decide (i ∉ a.val)

theorem readEq_value (i : I) {j k : Unit} (x y : Point I) (a : (source I).Atom j k)
    (ha : (source I).colour x y = some a) :
    x i = y i ↔ readEq I i a = true := by
  have hs := (colour_some I x y a).mp ha
  simp only [readEq,decide_eq_true_eq]
  rw [← hs,mem_support,not_not]

theorem semanticCCO : SemanticCCO.{0,u,z,u} (source I) := by
  intro V D hcycles
  have hl : ∀ i : I, ∃ label : V → ℕ,
      ∀ x y (h : x ≠ y) a, D.edge x y h = some a →
        (label x = label y ↔ readEq I i a = true) := by
    intro i
    exact CycleConsistency.coordinate_labels (source I) D (readEq I i)
      (fun _ => rfl) (fun _ x => x i) (fun _ _ a ha => readEq_value I i _ _ a ha) hcycles
  choose label hlabel using hl
  refine ⟨{
    point := fun x i => label i x
    preserves_edge := ?_
  }⟩
  intro x y h a ha
  apply (colour_some I _ _ a).mpr
  ext i
  have hh : label i x = label i y ↔ i ∉ a.val := by
    simpa only [readEq,decide_eq_true_eq] using hlabel i x y h a ha
  simpa only [mem_support,not_not] using not_congr hh

theorem ageAP : AgeAP (source I) := (source I).ageAP_of_homogeneous (homogeneous I)
end CCO.RealClosure.Bounds.Examples.Coordinate
