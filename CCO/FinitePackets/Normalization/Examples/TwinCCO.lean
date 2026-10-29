import CCO.FinitePackets.Normalization.Examples.TwinSource

/-! Actual homomorphic CCO, in arbitrary diagram universes. The two infinite
coordinates use actual specified-cycle consistency. The bit constraints are
solved on the t-only graph: other colours impose NO gain on the bit. -/
universe z
namespace CCO.FinitePackets.Normalization.Examples.Twin
open Colour
open CCO.RealClosure.Bounds.Examples.CycleConsistency
open CCO.SIR.Positive.Direct

variable {V : Type z} (D : PartialDiagram source V)

def twinGraph : SimpleGraph V where
  Adj x y := ∃ h : x ≠ y, D.edge x y h = some twin
  symm := ⟨by
    rintro x y ⟨h,ha⟩
    exact ⟨h.symm,(D.edge_reverse x y h twin).mp ha⟩⟩
  loopless := ⟨fun _ h => h.choose rfl⟩

private theorem bits_xor_of_twin {x y : Point} (h : colour x y = some twin) :
    (bit x ^^ bit y) = true := by
  have hn := (colour_twin x y).mp h |>.2.2
  cases hx : bit x <;> cases hy : bit y <;> simp_all

private theorem twin_cycle_parity (hcycles : ∀ C : SimpleCycle D, CycleHom C)
    (x : V) (p : (twinGraph D).Walk x x) (hp : p.IsCycle) :
    SignedWalk.parity (fun _ _ : V => true) p = false := by
  let C := cycleOfWalk (K := twinGraph D) D (fun _ _ h => ⟨h.choose,twin,h.choose_spec⟩) p hp
  obtain ⟨point,hpoint⟩ := hcycles C
  have hpos : 0 < p.length := lt_of_lt_of_le (by decide : 0 < 3) hp.three_le_length
  let val (i : Fin p.length) : Bool := bit (point i)
  have hs (i : Fin p.length) : (val i ^^ val (cyclicNext hpos i)) = true := by
    have ha : (twinGraph D).Adj (C.vertices i) (C.vertices (cyclicNext C.length_pos i)) := by
      change (twinGraph D).Adj (p.getVert i.val) (p.getVert ((i.val+1)%p.length))
      rw [closedWalk_next_getVert p hpos i]
      exact p.adj_getVert_succ i.isLt
    have hedge : D.edge (C.vertices i) (C.vertices (cyclicNext C.length_pos i))
        (C.next_ne i) = some twin := ha.choose_spec
    exact bits_xor_of_twin (hpoint i twin hedge)
  let f (n : ℕ) : Bool := val ⟨n % p.length,Nat.mod_lt _ hpos⟩
  have hf : f p.length = f 0 := by simp only [f,Nat.mod_self,Nat.zero_mod]
  have hsteps : ∀ n < p.length, true = (f n ^^ f (n+1)) := by
    intro n hn
    have hh := hs ⟨n,hn⟩
    simpa only [f,cyclicNext,Nat.mod_eq_of_lt hn] using hh.symm
  have hh := SignedWalk.parity_of_getVert (fun _ _ : V => true) p f hsteps
  simpa only [hf,Bool.xor_self] using hh

/-- A bipartite labelling of precisely the twin constraints, forced by actual
simple t-cycle homomorphisms. This does not assign parity to row/column edges. -/
theorem twin_labels (hcycles : ∀ C : SimpleCycle D, CycleHom C) :
    ∃ label : V → Bool, ∀ x y (h : x ≠ y),
      D.edge x y h = some twin → label x ≠ label y := by
  have hclosed := SignedWalk.closed_parity_zero (fun _ _ : V => true)
    (fun _ _ => rfl) (twin_cycle_parity D hcycles)
  obtain ⟨label,hl⟩ := SignedWalk.exists_potential (fun _ _ : V => true) hclosed
  refine ⟨label,?_⟩
  intro x y h ha
  have hh := hl x y ⟨h,ha⟩
  intro he
  rw [he,Bool.xor_self] at hh
  exact Bool.noConfusion hh

theorem semanticCCO : SemanticCCO.{0,0,z,0} source := by
  intro V D hcycles
  obtain ⟨r,hr⟩ := coordinate_labels source D rowRead (fun _ => rfl)
    (fun _ x => row x) (fun x y a ha => row_reader x y a ha) hcycles
  obtain ⟨c,hc⟩ := coordinate_labels source D columnRead (fun _ => rfl)
    (fun _ x => column x) (fun x y a ha => column_reader x y a ha) hcycles
  obtain ⟨b,hb⟩ := twin_labels D hcycles
  refine ⟨{point := fun v => (r v,c v,b v),preserves_edge := ?_}⟩
  intro x y h a ha
  have hrow := hr x y h a ha
  have hcol := hc x y h a ha
  cases a
  · apply (colour_twin _ _).mpr
    exact ⟨hrow.mpr rfl,hcol.mpr rfl,hb x y h ha⟩
  · apply (colour_row _ _).mpr
    exact ⟨hrow.mpr rfl,fun he => Bool.noConfusion (hcol.mp he)⟩
  · apply (colour_column _ _).mpr
    exact ⟨fun he => Bool.noConfusion (hrow.mp he),hcol.mpr rfl⟩
  · apply (colour_apart _ _).mpr
    exact ⟨fun he => Bool.noConfusion (hrow.mp he),fun he => Bool.noConfusion (hcol.mp he)⟩

end CCO.FinitePackets.Normalization.Examples.Twin
