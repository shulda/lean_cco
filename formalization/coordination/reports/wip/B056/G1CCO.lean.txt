import CCO.GuardedTwoRoot.G1Model
import CCO.RealClosure.Bounds.Examples.CycleConsistency
import CCO.SimultaneousQuotients.Boundaries.PhaseSource

/-! C41: same-block constraints and within-block parity constraints are
solved separately, from the SAME actual cycle hypotheses. r imposes no
bit equation; it is erased only in the auxiliary parity diagram. Fresh
clone codes prevent every forbidden logical real diagonal. -/

universe z
namespace CCO.GuardedTwoRoot.G1
open CCO.RealClosure.Bounds.Examples
open CCO.SimultaneousQuotients.Boundaries
noncomputable section

def blockFlag (a : Atom) : Bool := decide (a ≠ r)
def blockRead : CycleConsistency.Reader source := fun {_ _} (a : Atom) => blockFlag a
def gain (a : Atom) : Bool := decide (a = q)

theorem block_read_value (x y : Real) (a : Atom) (ha : colour x y = some a) :
    block x = block y ↔ blockFlag a = true := by
  fin_cases a
  · exact ⟨fun _ => rfl,fun _ => ((colour_p x y).mp ha).2.1⟩
  · exact ⟨fun _ => rfl,fun _ => ((colour_q x y).mp ha).1⟩
  · exact ⟨fun h => False.elim (((colour_r x y).mp ha) h),by simp [blockFlag]⟩

theorem gain_value (x y : Real) (a : Atom) (hr : a ≠ r)
    (ha : colour x y = some a) : (bit x ^^ bit y) = gain a := by
  fin_cases a
  · have hb := ((colour_p x y).mp ha).2.2
    simp [gain,hb]
  · have hb := ((colour_q x y).mp ha).2
    cases hx : bit x <;> cases hy : bit y <;> simp_all [gain]
  · exact False.elim (hr rfl)

variable {V : Type z} (D : PartialDiagram source V)

def parityEdge (x y : V) (h : x ≠ y) : Option Bool :=
  (D.edge x y h).bind (fun (a : Atom) => if a = r then none else some (gain a))

theorem parityEdge_some {x y : V} {h : x ≠ y} {b : Bool}
    (hb : parityEdge D x y h = some b) :
    ∃ a : Atom, D.edge x y h = some a ∧ a ≠ r ∧ gain a = b := by
  cases ha : D.edge x y h with
  | none =>
    have hnone : parityEdge D x y h = none := by
      unfold parityEdge
      rw [ha]
      rfl
    rw [hnone] at hb
    cases hb
  | some a =>
    change Atom at a
    have hsome : parityEdge D x y h = (if a = r then none else some (gain a)) := by
      unfold parityEdge
      rw [ha]
      rfl
    rw [hsome] at hb
    by_cases hr : a = r
    · rw [if_pos hr] at hb
      cases hb
    · rw [if_neg hr] at hb
      exact ⟨a,rfl,hr,Option.some.inj hb⟩

theorem old_edge_reverse (x y : V) (h : x ≠ y) :
    D.edge x y h = D.edge y x h.symm := by
  cases ha : D.edge x y h with
  | some a => exact ((D.edge_reverse x y h a).mp ha).symm
  | none =>
    cases hb : D.edge y x h.symm with
    | none => rfl
    | some a =>
      have hh := (D.edge_reverse y x h.symm a).mp hb
      rw [ha] at hh
      cases hh

def parityDiagram : PartialDiagram (Phase.source Unit) V where
  finite_type := D.finite_type
  vertexSort _ := ()
  edge := parityEdge D
  edge_reverse x y h b := by
    change parityEdge D x y h = some b ↔ parityEdge D y x h.symm = some b
    unfold parityEdge
    rw [old_edge_reverse D x y h]

theorem parity_cycles (hcycles : ∀ C : SimpleCycle D, CycleHom C)
    (C : SimpleCycle (parityDiagram D)) : CycleHom C := by
  let old : SimpleCycle D := {
    length := C.length
    length_ge_three := C.length_ge_three
    length_pos := C.length_pos
    vertices := C.vertices
    next_ne := C.next_ne
    specified := by
      intro p
      obtain ⟨b,hb⟩ := C.specified p
      obtain ⟨a,ha,_,_⟩ := parityEdge_some D hb
      exact ⟨a,ha⟩ }
  obtain ⟨point,hpoint⟩ := hcycles old
  refine ⟨fun p => ⟨bit (point p),p.val⟩,?_⟩
  intro p b hb
  obtain ⟨a,ha,hr,hgain⟩ := parityEdge_some D hb
  apply (Phase.colour_some Unit _ _ b).mpr
  refine ⟨?_,?_⟩
  · intro he
    have hp : p = cyclicNext C.length_pos p :=
      Fin.ext (congrArg (fun x : Phase.Tagged Unit => x.2.index) he)
    exact C.next_ne p (congrArg C.vertices hp)
  · exact (gain_value _ _ a hr (hpoint p a ha)).trans hgain

/-- Actual old homomorphic simple-cycle CCO. No terminal index,
hidden SAP, parity-consistency provider or finite-window surrogate. -/
theorem semanticCCO : SemanticCCO.{0,0,z,0} source := by
  intro V D hcycles
  obtain ⟨label,hLabel⟩ := CycleConsistency.coordinate_labels source D blockRead
    (fun _ => rfl) (fun _ x => block x)
    (fun x y a ha => block_read_value x y a ha) hcycles
  obtain ⟨phase⟩ := Phase.semanticCCO Unit V (parityDiagram D)
    (parity_cycles D hcycles)
  classical
  letI : Finite V := D.finite_type
  letI : Fintype V := Fintype.ofFinite _
  let code := Fintype.equivFin V
  refine ⟨{
    point := fun v => ((label v,(phase.point v).phase),(code v).val)
    preserves_edge := ?_ }⟩
  intro x y hxy a ha
  change Atom at a
  change colour ((label x,(phase.point x).phase),(code x).val)
    ((label y,(phase.point y).phase),(code y).val) = some a
  have hb := hLabel x y hxy a ha
  change label x = label y ↔ blockFlag a = true at hb
  have hNe : ((label x,(phase.point x).phase),(code x).val) ≠
      ((label y,(phase.point y).phase),(code y).val) := by
    intro he
    exact hxy (code.injective (Fin.ext (congrArg Prod.snd he)))
  have hGain (hr : a ≠ r) : ((phase.point x).phase ^^ (phase.point y).phase) = gain a := by
    have hedge : (parityDiagram D).edge x y hxy = some (gain a) := by
      change parityEdge D x y hxy = some (gain a)
      unfold parityEdge
      rw [ha]
      change (if a = r then none else some (gain a)) = some (gain a)
      rw [if_neg hr]
    exact ((Phase.colour_some Unit _ _ (gain a)).mp
      (phase.preserves_edge x y hxy (gain a) hedge)).2
  fin_cases a
  · apply (colour_p _ _).mpr
    have hSame : (phase.point x).phase = (phase.point y).phase := by
      have h := hGain (by decide)
      cases hx : (phase.point x).phase <;> cases hy : (phase.point y).phase <;>
        simp_all [gain]
    exact ⟨hNe,hb.mpr rfl,hSame⟩
  · apply (colour_q _ _).mpr
    have hOpp : (phase.point x).phase ≠ (phase.point y).phase := by
      have h := hGain (by decide)
      intro he
      simp [gain,he] at h
    exact ⟨hb.mpr rfl,hOpp⟩
  · apply (colour_r _ _).mpr
    intro he
    have hh := hb.mp he
    simp [blockFlag] at hh

end
end CCO.GuardedTwoRoot.G1
