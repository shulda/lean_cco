import CCO.StrongExact.CycleCompletion

/-!
# B050 C34: original SemanticCCO is universe-independent on finite diagrams

The fixed original SemanticCCO provider for finite old typed diagrams
was declared at vertex universe `max u v`. The actual accepted B002
private-word expansion has a genuinely finite vertex type at universe
zero. We transport the ENTIRE original finite diagram, its ACTUAL
simple cycles, and the resulting original homomorphism across ULift.

This is a proof-theoretic universe/finite-carrier equivalence, NOT a
second SemanticCCO hypothesis, an added source axiom, or an extra
cycle-realization oracle. All source colours and original typed edge
constraints remain LITERALLY the same.
-/

universe u v w z

namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- Actual downward map of an ULift is injective, regardless of the
universe at which the original old-source diagram is represented. -/
private theorem originalULift_down_injective {V : Type}
    (x y : ULift.{z} V)
    (h : x.down = y.down) : x = y := by
  cases x with
  | up a =>
    cases y with
    | up b =>
      cases h
      rfl

private theorem originalULift_down_ne {V : Type}
    (x y : ULift.{z} V) (h : x ≠ y) :
    x.down ≠ y.down := by
  intro hdown
  exact h (originalULift_down_injective x y hdown)

/-- Exact transport of a finite partial original OLD atomic diagram
to the universe required by the accepted original CCO provider. -/
private noncomputable def originalULiftDiagram
    {V : Type} (D : PartialDiagram S V) :
    PartialDiagram S (ULift.{z} V) := by
  letI : Finite V := D.finite_type
  refine {
    finite_type := inferInstance
    vertexSort := fun x => D.vertexSort x.down
    edge := fun x y h => D.edge x.down y.down
      (originalULift_down_ne x y h)
    edge_reverse := ?_ }
  intro x y h a
  exact D.edge_reverse x.down y.down
    (originalULift_down_ne x y h) a

/-- Every TRUE old specified simple cycle of the lifted diagram
projects to a simple cycle of the concrete original finite diagram,
with the same cyclic order, specified source atom and sort at each
original edge. -/
private noncomputable def originalULiftCycleDown
    {V : Type} (D : PartialDiagram S V)
    (C : SimpleCycle (originalULiftDiagram S D)) :
    SimpleCycle D where
  length := C.length
  length_ge_three := C.length_ge_three
  length_pos := C.length_pos
  vertices := ⟨fun k => (C.vertices k).down, by
    intro a b hab
    apply C.vertices.injective
    exact originalULift_down_injective _ _ hab⟩
  next_ne := by
    intro k h
    exact C.next_ne k (originalULift_down_injective _ _ h)
  specified := by
    intro k
    exact C.specified k

/-- A real original source homomorphism of the projected cycle is
also a homomorphism of the SAME lifted cycle. No vertex collision or
surrogate edge is introduced. -/
private theorem originalULiftCycleHom
    {V : Type} (D : PartialDiagram S V)
    (C : SimpleCycle (originalULiftDiagram S D))
    (h : CycleHom (originalULiftCycleDown S D C)) :
    CycleHom C := by
  obtain ⟨point,hEdge⟩ := h
  refine ⟨point, ?_⟩
  intro k a h
  exact hEdge k a h

/-- The one ORIGINAL SemanticCCO statement at the repository's
standard source vertex universe implies SemanticCCO at universe 0,
where the genuine B002 private-word diagrams happen to live.

Every graph/edge/cycle/realization is transported along a finite
bijection; neither a second CCO assumption nor a new axiom appears. -/
theorem originalSemanticCCO_finite_universe_zero
    (cco : SemanticCCO.{u,v,max u v,w} S) :
    SemanticCCO.{u,v,0,w} S := by
  intro V D hCycles
  let lifted : PartialDiagram S (ULift.{max u v} V) := originalULiftDiagram S D
  have hLiftCycles : ∀ C : SimpleCycle lifted, CycleHom C := by
    intro C
    exact originalULiftCycleHom S D C
      (hCycles (originalULiftCycleDown S D C))
  obtain ⟨f⟩ := cco (ULift.{max u v} V) lifted hLiftCycles
  let result : DiagramHom D := {
    point := fun x => f.point (ULift.up x : ULift.{max u v} V)
    preserves_edge := by
      intro x y hxy a hEdge
      have hLiftNe :
          (ULift.up x : ULift.{max u v} V) ≠ ULift.up y := by
        intro h
        exact hxy (congrArg ULift.down h)
      have hLiftEdge :
          lifted.edge (ULift.up x) (ULift.up y) hLiftNe = some a := by
        change D.edge x y
          (originalULift_down_ne (ULift.up x) (ULift.up y) hLiftNe) = some a
        exact hEdge
      exact f.preserves_edge (ULift.up x) (ULift.up y) hLiftNe a hLiftEdge }
  exact ⟨result⟩

end CCO.TerminalLattice
