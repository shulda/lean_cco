import CCO.RealHull.Geometry.FibreNewCycle
import CCO.RealHull.Geometry.SerialCycle
import CCO.StrongExact.CycleIndexRotation

/-! Genuine CCO of the actual realised fibre. A mixed simple cycle is
rotated to an actual anchor; specified edges are followed serially in the
fibre, with resets at literal anchors. The closing singleton forces the
last edge. All-new cycles are literal input cycles. Original CCO then
completes ONE shared anchored diagram, whose WHOLE anchor is aligned.
No SAP, globalisation, quotient CCO or other completion provider is used.
-/

universe v w z t
namespace CCO.RealHull.Geometry

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable [DecidableEq M] (A : Finset M) (q : ↥A → Atom S)
variable [Nonempty (FibreSet S A q)] {V : Type z}
variable {G : Type t} [Group G] [MulAction G M]

theorem fibre_cycleHom_of_anchor_zero (H : HomogeneousSource S G)
    (D : PartialDiagram (fibreSource S A q) V)
    (C : SimpleCycle (fibreAnchorDiagram S A q D))
    (a : ↥A) (hzero : C.vertices ⟨0,C.length_pos⟩ = Sum.inr a) : CycleHom C := by
  apply cycleHom_of_singleton_serial S _ C (FibreVertexRealizes S A q) a.val
  · intro p
    rw [hzero]
    rfl
  · intro i p hp
    obtain ⟨c,hc⟩ := C.specified i
    obtain ⟨r,hr,hedge⟩ := fibreAnchor_edge_serial S A q H D _ _ (C.next_ne i) c hc p hp
    refine ⟨r,hr,?_⟩
    intro d hd
    have heq : c = d := Option.some.inj (hc.symm.trans hd)
    exact hedge.trans (congrArg some heq)

theorem fibreAnchor_cycleHom (H : HomogeneousSource S G)
    (D : PartialDiagram (fibreSource S A q) V)
    (hcycles : ∀ C : SimpleCycle D, CycleHom C)
    (C : SimpleCycle (fibreAnchorDiagram S A q D)) : CycleHom C := by
  classical
  by_cases hnew : ∀ p, ∃ x : V, C.vertices p = Sum.inl x
  · exact fibre_cycleHom_of_all_new S A q D C hnew hcycles
  · have hex : ∃ p, ¬ ∃ x : V, C.vertices p = Sum.inl x := by
      simpa only [not_forall] using hnew
    obtain ⟨p,hp⟩ := hex
    cases he : C.vertices p with
    | inl x => exact False.elim (hp ⟨x,he⟩)
    | inr a =>
      apply (C.cycleHom_rotate_iff p).mp
      apply fibre_cycleHom_of_anchor_zero S A q H D (C.rotate p) a
      exact (C.rotate_zero_vertices p).trans he

theorem fibre_semanticCCO (H : HomogeneousSource S G)
    (cco : SemanticCCO.{0,v,0,w} S) :
    SemanticCCO.{0,v,z,w} (fibreSource S A q) := by
  intro V D hcycles
  obtain ⟨f⟩ := (CCO.semanticCCO_change_universe S cco) _
    (fibreAnchorDiagram S A q D) (fibreAnchor_cycleHom S A q H D hcycles)
  obtain ⟨point,hpoint,_⟩ := align_fibre_anchor S A q H D f
  exact ⟨{
    point := point
    preserves_edge := by
      intro x y hxy c hc
      exact (inducedColour_some_iff S () _ _ _ c).mpr (hpoint x y hxy c hc)
  }⟩

end CCO.RealHull.Geometry
