import CCO.RealClosure.Bounds.Examples.PhaseSource

/-! Actual arbitrary-universe homomorphic CCO of the infinite Cartesian
phase source. Two coordinate equality systems and the one Boolean gain
system are solved simultaneously from genuine specified simple cycles. -/
universe z
namespace CCO.RealClosure.Bounds.Examples.Phase
open CCO.RealClosure.Bounds.Examples.CycleConsistency

private theorem row_reader {i j : Unit} (x y : Point) (a : source.Atom i j)
    (ha : source.colour x y = some a) :
    row x = row y ↔ a.val.1 = true := by
  have hh := congrArg Prod.fst ((colour_some x y a).mp ha)
  change decide (row x = row y) = a.val.1 at hh
  rw [← hh]
  simp

private theorem column_reader {i j : Unit} (x y : Point) (a : source.Atom i j)
    (ha : source.colour x y = some a) :
    column x = column y ↔ a.val.2.1 = true := by
  have hh := congrArg (fun p : Pattern => p.2.1) ((colour_some x y a).mp ha)
  change decide (column x = column y) = a.val.2.1 at hh
  rw [← hh]
  simp

private theorem gain_reader {i j : Unit} (x y : Point) (a : source.Atom i j)
    (ha : source.colour x y = some a) :
    (phase x ^^ phase y) = a.val.2.2 :=
  congrArg (fun p : Pattern => p.2.2) ((colour_some x y a).mp ha)

theorem semanticCCO : SemanticCCO.{0,0,z,0} source := by
  intro V D hcycles
  obtain ⟨r,hr⟩ := coordinate_labels source D (fun a => a.val.1) (fun _ => rfl)
    (fun _ x => row x) (fun x y a ha => row_reader x y a ha) hcycles
  obtain ⟨c,hc⟩ := coordinate_labels source D (fun a => a.val.2.1) (fun _ => rfl)
    (fun _ x => column x) (fun x y a ha => column_reader x y a ha) hcycles
  obtain ⟨g,hg⟩ := phase_labels source D (fun a => a.val.2.2) (fun _ => rfl)
    (fun _ x => phase x) (fun x y a ha => gain_reader x y a ha) hcycles
  refine ⟨{
    point := fun v => (r v,c v,g v)
    preserves_edge := ?_
  }⟩
  intro x y h a ha
  apply (colour_some _ _ a).mpr
  have hrow : decide (r x = r y) = a.val.1 := by
    have hh := hr x y h a ha
    cases hb : a.val.1 <;> simp_all
  have hcol : decide (c x = c y) = a.val.2.1 := by
    have hh := hc x y h a ha
    cases hb : a.val.2.1 <;> simp_all
  exact Prod.ext hrow (Prod.ext hcol (hg x y h a ha))

end CCO.RealClosure.Bounds.Examples.Phase
