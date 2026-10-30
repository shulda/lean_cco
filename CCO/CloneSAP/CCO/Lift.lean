import CCO.CloneSAP.Basic
import Mathlib.Data.Fintype.EquivFin

/-! Actual finite fresh-index lifts. These separate the elementary real
injectivity from the owner-existence theorem, and keep missing edges free. -/
universe u v w z
set_option backward.isDefEq.respectTransparency.types false
namespace CCO.CloneSAP.CCO
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {V : Type z}

/-- C20/C36: any finite compatible owner assignment has a globally injective
actual clone realization. The assumptions speak only of specified edges. -/
theorem lift_owner_assignment (D : PartialDiagram (source S) V)
    (p : ∀ x : V, X (D.vertexSort x))
    (old : ∀ x y h a, D.edge x y h = some (.inl a) →
      S.colour (p x) (p y) = some a)
    (clones : ∀ x y h e, D.edge x y h = some (.inr e) →
      (⟨D.vertexSort x,p x⟩ : Sigma X) = ⟨D.vertexSort y,p y⟩) :
    ∃ f : DiagramHom D, f.IsInjective := by
  classical
  letI : Finite V := D.finite_type
  letI : Fintype V := Fintype.ofFinite V
  let n : V ↪ ℕ := (Fintype.equivFin V).toEmbedding.trans
    ⟨Fin.val,Fin.val_injective⟩
  let f : DiagramHom D := {
    point x := (p x,n x)
    preserves_edge := by
      intro x y h a ha
      cases a with
      | inl a => exact (colour_old_iff S _ _ a).mpr (old x y h a ha)
      | inr e => exact (colour_clone_iff S _ _ e).mpr ⟨clones x y h e ha,
          fun he => h (n.injective he)⟩ }
  refine ⟨f,?_⟩
  intro x y h
  exact n.injective (congrArg (fun x : Sigma (Carrier X) => x.2.2) h)

/-- Regard an old diversity partial graph upstairs using ONLY its old atoms.
No equality constraint or new c-edge is inserted. -/
def oldDiagram (D : PartialDiagram S V) : PartialDiagram (source S) V where
  finite_type := D.finite_type
  vertexSort := D.vertexSort
  edge x y h := (D.edge x y h).map Sum.inl
  edge_reverse x y h a := by
    cases a with
    | inl a =>
      change (D.edge x y h).map Sum.inl = some (.inl a) ↔
        (D.edge y x h.symm).map Sum.inl = some (.inl (S.conv a))
      simpa using D.edge_reverse x y h a
    | inr e =>
      change (D.edge x y h).map Sum.inl = some (.inr e) ↔
        (D.edge y x h.symm).map Sum.inl = some
          (.inr (⟨e.down.symm⟩ : PLift (D.vertexSort y = D.vertexSort x)))
      cases D.edge x y h <;> cases D.edge y x h.symm <;> simp

@[simp] theorem oldDiagram_edge (D : PartialDiagram S V) (x y : V) (h : x ≠ y)
    (a : S.Atom (D.vertexSort x) (D.vertexSort y)) :
    (oldDiagram S D).edge x y h = some (.inl a) ↔ D.edge x y h = some a := by
  change (D.edge x y h).map Sum.inl = some (.inl a) ↔ _
  cases D.edge x y h <;> simp

theorem oldDiagram_specified (D : PartialDiagram S V) (x y : V) (h : x ≠ y)
    (c : (source S).Atom (D.vertexSort x) (D.vertexSort y))
    (hc : (oldDiagram S D).edge x y h = some c) :
    ∃ a, c = .inl a ∧ D.edge x y h = some a := by
  change (D.edge x y h).map Sum.inl = some c at hc
  cases he : D.edge x y h with
  | none => simp [he] at hc
  | some a =>
    rw [he] at hc
    change some (.inl a : Atom S (D.vertexSort x) (D.vertexSort y)) = some c at hc
    have hh : .inl a = c := Option.some.inj hc
    exact ⟨a,hh.symm,rfl⟩

/-- A cycle in the lifted old-only graph is a literal old diversity cycle. -/
def oldCycle (D : PartialDiagram S V) (C : SimpleCycle (oldDiagram S D)) :
    SimpleCycle D where
  length := C.length
  length_ge_three := C.length_ge_three
  length_pos := C.length_pos
  vertices := C.vertices
  next_ne := C.next_ne
  specified p := by
    obtain ⟨c,hc⟩ := C.specified p
    obtain ⟨a,_,ha⟩ := oldDiagram_specified S D _ _ _ c hc
    exact ⟨a,ha⟩

/-- Each old cycle solution lifts independently, even when old nonadjacent
vertices collide. Distinct cycle indices can be used for every lift. -/
theorem oldDiagram_cycles (D : PartialDiagram S V)
    (cycles : ∀ C : SimpleCycle D, CycleHom C) :
    ∀ C : SimpleCycle (oldDiagram S D), CycleHom C := by
  intro C
  obtain ⟨point,hpoint⟩ := cycles (oldCycle S D C)
  refine ⟨fun p => (point p,p.val),?_⟩
  intro p c hc
  obtain ⟨a,rfl,ha⟩ := oldDiagram_specified S D _ _ _ c hc
  exact (colour_old_iff S _ _ a).mpr (hpoint p a ha)

/-- C22: the converse needs only upstairs HOM CCO and literal projection.
The individual cycle lifts are not required to be coherent with one another. -/
theorem cco_reflects (cco : SemanticCCO.{u,v,z,w} (source S)) :
    SemanticCCO.{u,v,z,w} S := by
  intro V D cycles
  obtain ⟨f⟩ := cco V (oldDiagram S D) (oldDiagram_cycles S D cycles)
  exact ⟨{
    point x := (f.point x).1
    preserves_edge := by
      intro x y h a ha
      exact (colour_old_iff S _ _ a).mp (f.preserves_edge x y h (.inl a)
        ((oldDiagram_edge S D x y h a).mpr ha)) }⟩

end CCO.CloneSAP.CCO
