import CCO.FiniteFibres.Boundaries.DifferenceCCO
import CCO.RelationalCompletion.Atomic.Class

/-! The difference completion theorem is connected to the already accepted
arbitrary-palette atomic diagram and simple-cycle types. In particular the
directed C3 and infinite F2 examples use every genuine finite atomic request,+not an unrelated global consistency predicate. -/
namespace CCO.FiniteFibres.Boundaries.Difference
open RelationalCompletion.Atomic

variable (A : Type*) [AddCommGroup A]

def palette : Palette where
  Sorts := Unit
  Atom := Difference.Atom A
  src _ := ()
  tgt _ := ()
  conv := converse A
  conv_conv := converse_involutive A
  src_conv _ := rfl
  tgt_conv _ := rfl

namespace AtomicDiagram
variable {A} {n : ℕ} (D : RelationalCompletion.Atomic.Diagram (palette A) n)

def differences : Difference.Diagram A (Fin n) where
  edge := D.edge
  edge_self := D.edge_self
  edge_reverse := D.edge_reverse

def Hom (f : Fin n → A) : Prop :=
  ∀ x y a, D.edge x y = some a → (source A).binary a (f x) (f y)

def CycleHom (C : RelationalCompletion.Atomic.SimpleCycle D) : Prop :=
  ∃ f : Fin C.length → A, ∀ p a,
    D.edge (C.vertices p) (C.vertices (cyclicNext (by have := C.length_ge_three; omega) p)) = some a →
      (source A).binary a (f p) (f (cyclicNext (by have := C.length_ge_three; omega) p))

theorem next_getVert {x : Fin n} (p : (differences D).graph.Walk x x) (hp : p.IsCycle)
    (i : Fin p.length) :
    p.getVert ((i.val+1)%p.length) = p.getVert (i.val+1) := by
  by_cases h : i.val+1 < p.length
  · rw [Nat.mod_eq_of_lt h]
  · have he : i.val+1 = p.length := by omega
    simp only [he,Nat.mod_self,SimpleGraph.Walk.getVert_zero,SimpleGraph.Walk.getVert_length]

/-- Literal conversion of each actual simple graph cycle to the accepted
atomic cycle, preserving every original directed atom around its closure. -/
def cycleOfWalk {x : Fin n} (p : (differences D).graph.Walk x x) (hp : p.IsCycle) :
    RelationalCompletion.Atomic.SimpleCycle D where
  length := p.length
  length_ge_three := hp.three_le_length
  vertices := {
    toFun i := p.getVert i.val
    inj' := by
      intro i j hij
      apply Fin.ext
      exact hp.getVert_injOn' (by change i.val ≤ p.length-1; omega)
        (by change j.val ≤ p.length-1; omega) hij }
  specified i := by
    have h := p.adj_getVert_succ i.isLt
    obtain ⟨a,ha⟩ := h
    refine ⟨a,?_⟩
    change D.edge (p.getVert i.val) (p.getVert ((i.val+1)%p.length)) = some a
    rw [next_getVert D p hp i]
    exact ha

set_option backward.isDefEq.respectTransparency.types false in
theorem walkCycleHom
    (hc : ∀ C : RelationalCompletion.Atomic.SimpleCycle D, CycleHom D C)
    {x : Fin n} (p : (differences D).graph.Walk x x) (hp : p.IsCycle) :
    (differences D).CycleHom p := by
  let C := cycleOfWalk D p hp
  obtain ⟨point,hpoint⟩ := hc C
  have hpos : 0 < p.length := lt_of_lt_of_le (by decide : 0 < 3) hp.three_le_length
  let f : ℕ → A := fun k => point ⟨k%p.length,Nat.mod_lt _ hpos⟩
  refine ⟨f,?_,?_⟩
  · simp only [f,Nat.mod_self,Nat.zero_mod]
  · intro k hk a ha
    let i : Fin p.length := ⟨k,hk⟩
    have hi : (⟨k%p.length,Nat.mod_lt _ hpos⟩ : Fin p.length) = i :=
      Fin.ext (Nat.mod_eq_of_lt hk)
    have hh := hpoint i a
    have hEdge : D.edge (C.vertices i)
        (C.vertices (cyclicNext (by have := C.length_ge_three; omega) i)) = some a := by
      change D.edge (p.getVert k) (p.getVert ((k+1)%p.length)) = some a
      rw [next_getVert D p hp i]
      exact ha
    have hReal := hh hEdge
    change (source A).binary a (point i) (point ⟨(k+1)%p.length,_⟩) at hReal
    change (source A).binary a (point ⟨k%p.length,_⟩) (point ⟨(k+1)%p.length,_⟩)
    simpa only [C,cycleOfWalk,i,Nat.mod_eq_of_lt hk] using hReal

/-- Every accepted finite arbitrary-palette atomic request is completed
from its actual simple-cycle homomorphisms into this infinite or finite
named difference structure. No locally allowedness callback is needed:
each nonzero difference atom is actually realized. -/
theorem semanticCCO
    (hc : ∀ C : RelationalCompletion.Atomic.SimpleCycle D, CycleHom D C) :
    ∃ f : Fin n → A, Hom D f :=
  (differences D).hom_of_simple_cycles (fun _ p hp => walkCycleHom D hc p hp)

end AtomicDiagram
end CCO.FiniteFibres.Boundaries.Difference
