import CCO.RealHull.Geometry.FibreSerial

/-! A simple cycle lying entirely among the new formal fibre vertices is
literally a simple cycle of the ORIGINAL input fibre diagram. No cycle
completion or unproved mixed-cycle classification is used here. -/

universe v w z
namespace CCO.RealHull.Geometry

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable [DecidableEq M] (A : Finset M) (q : ↥A → Atom S)
variable [Nonempty (FibreSet S A q)] {V : Type z}
variable (D : PartialDiagram (fibreSource S A q) V)
variable (C : SimpleCycle (fibreAnchorDiagram S A q D))
variable (hnew : ∀ p, ∃ x : V, C.vertices p = Sum.inl x)

private theorem edge_transport {x y x' y' : V ⊕ ↥A} (hx : x = x') (hy : y = y')
    (h : x ≠ y) (h' : x' ≠ y') (a : Atom S) :
    (fibreAnchorDiagram S A q D).edge x y h = some a ↔
      (fibreAnchorDiagram S A q D).edge x' y' h' = some a := by
  cases hx
  cases hy
  rfl

noncomputable def fibreCycleVertex (p : Fin C.length) : V := Classical.choose (hnew p)

theorem fibreCycleVertex_spec (p : Fin C.length) :
    C.vertices p = Sum.inl (fibreCycleVertex S A q D C hnew p) := Classical.choose_spec (hnew p)

theorem fibreCycleVertex_injective : Function.Injective (fibreCycleVertex S A q D C hnew) := by
  intro p r hpr
  apply C.vertices.injective
  exact (fibreCycleVertex_spec S A q D C hnew p).trans
    ((congrArg Sum.inl hpr).trans (fibreCycleVertex_spec S A q D C hnew r).symm)

theorem fibreCycleVertex_next_ne (p : Fin C.length) :
    fibreCycleVertex S A q D C hnew p ≠
      fibreCycleVertex S A q D C hnew (cyclicNext C.length_pos p) := by
  intro he
  apply C.next_ne p
  exact (fibreCycleVertex_spec S A q D C hnew p).trans
    ((congrArg Sum.inl he).trans
      (fibreCycleVertex_spec S A q D C hnew (cyclicNext C.length_pos p)).symm)

theorem fibreCycle_edge_pullback (p : Fin C.length) (a : Atom S)
    (ha : (fibreAnchorDiagram S A q D).edge (C.vertices p)
      (C.vertices (cyclicNext C.length_pos p)) (C.next_ne p) = some a) :
    ∃ c, D.edge (fibreCycleVertex S A q D C hnew p)
      (fibreCycleVertex S A q D C hnew (cyclicNext C.length_pos p))
      (fibreCycleVertex_next_ne S A q D C hnew p) = some c ∧ c.val = a := by
  apply Option.map_eq_some_iff.mp
  exact (edge_transport S A q D
    (fibreCycleVertex_spec S A q D C hnew p)
    (fibreCycleVertex_spec S A q D C hnew (cyclicNext C.length_pos p)) _
    (fun he => fibreCycleVertex_next_ne S A q D C hnew p (Sum.inl.inj he)) a).mp ha

noncomputable def fibreCycleOfAllNew : SimpleCycle D where
  length := C.length
  length_ge_three := C.length_ge_three
  length_pos := C.length_pos
  vertices := ⟨fibreCycleVertex S A q D C hnew, fibreCycleVertex_injective S A q D C hnew⟩
  next_ne := fibreCycleVertex_next_ne S A q D C hnew
  specified := by
    intro p
    obtain ⟨a,ha⟩ := C.specified p
    obtain ⟨c,hc,_⟩ := fibreCycle_edge_pullback S A q D C hnew p a ha
    exact ⟨c,hc⟩

include hnew in
theorem fibre_cycleHom_of_all_new
    (hcycles : ∀ E : SimpleCycle D, CycleHom E) : CycleHom C := by
  obtain ⟨point,hpoint⟩ := hcycles (fibreCycleOfAllNew S A q D C hnew)
  refine ⟨fun p => (point p).val,?_⟩
  intro p a ha
  obtain ⟨c,hc,hca⟩ := fibreCycle_edge_pullback S A q D C hnew p a ha
  have hh := hpoint p c hc
  have ho := (inducedColour_some_iff S () _ _ _ c).mp hh
  exact ho.trans (congrArg some hca)

end CCO.RealHull.Geometry
