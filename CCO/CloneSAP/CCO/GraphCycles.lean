import CCO.Finite
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! Generic literal graph-cycle support for the clone contraction proof.
This module proves its own conversion to the original finite diversity-cycle
interface; no equality-labelled completion theorem is assumed. -/
universe u v w z
set_option backward.isDefEq.respectTransparency.types false
namespace CCO.CloneSAP.CCO
variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}
variable {V : Type z} (D : PartialDiagram S V)

def graph : SimpleGraph V where
  Adj x y := ∃ h : x ≠ y, ∃ a, D.edge x y h = some a
  symm.symm := by
    rintro x y ⟨h,a,ha⟩
    exact ⟨h.symm,S.conv a,(D.edge_reverse x y h a).mp ha⟩
  loopless.irrefl := by
    rintro x ⟨h,_⟩
    exact h rfl

/-- A graph-theoretic simple closed walk supplies a genuine simple cycle
of the original typed partial diagram, of length at least three. -/
def walkSimpleCycle {x : V} (p : (graph D).Walk x x) (hp : p.IsCycle) :
    SimpleCycle D where
  length := p.length
  length_ge_three := hp.three_le_length
  length_pos := by have := hp.three_le_length; omega
  vertices := {
    toFun i := p.getVert i.val
    inj' := by
      intro i j hij
      apply Fin.ext
      exact hp.getVert_injOn' (by change i.val ≤ p.length - 1; omega)
        (by change j.val ≤ p.length - 1; omega) hij }
  next_ne i := by
    have hnext : p.getVert (cyclicNext (by have := hp.three_le_length; omega) i).val =
        p.getVert (i.val+1) := by
      by_cases h : i.val+1 < p.length
      · simp [cyclicNext,Nat.mod_eq_of_lt h]
      · have he : i.val+1 = p.length := by omega
        simp [cyclicNext,he]
    change p.getVert i.val ≠ p.getVert (cyclicNext _ i).val
    rw [hnext]
    exact (p.adj_getVert_succ i.isLt).ne
  specified i := by
    have hnext : p.getVert (cyclicNext (by have := hp.three_le_length; omega) i).val =
        p.getVert (i.val+1) := by
      by_cases h : i.val+1 < p.length
      · simp [cyclicNext,Nat.mod_eq_of_lt h]
      · have he : i.val+1 = p.length := by omega
        simp [cyclicNext,he]
    have hadj : (graph D).Adj (p.getVert i.val)
        (p.getVert (cyclicNext (by have := hp.three_le_length; omega) i).val) := by
      simpa only [hnext] using p.adj_getVert_succ i.isLt
    obtain ⟨h,a,ha⟩ := hadj
    exact ⟨a,ha⟩

/-- Extend a cycle homomorphism to an arbitrary typed point assignment on
all formal vertices. Only the actual cycle edges are claimed preserved. -/
theorem cycleHom_global {C : SimpleCycle D} (h : CycleHom C) :
    ∃ f : ∀ x : V, X (D.vertexSort x),
      ∀ p h a, D.edge (C.vertices p) (C.vertices (cyclicNext C.length_pos p))
        h = some a →
        S.colour (f (C.vertices p)) (f (C.vertices (cyclicNext C.length_pos p))) = some a := by
  classical
  obtain ⟨point,hpoint⟩ := h
  let f : ∀ x : V, X (D.vertexSort x) := fun x =>
    if h : ∃ p, C.vertices p = x then
      (congrArg D.vertexSort (Classical.choose_spec h)) ▸ point (Classical.choose h)
    else Classical.choice (S.nonemptySort (D.vertexSort x))
  have hf (p : Fin C.length) : f (C.vertices p) = point p := by
    dsimp [f]
    rw [dif_pos ⟨p,rfl⟩]
    have cast_value (q : Fin C.length) (hv : C.vertices q = C.vertices p) :
        (congrArg D.vertexSort hv) ▸ point q = point p := by
      have hq := C.vertices.injective hv
      subst q
      rfl
    exact cast_value _ (Classical.choose_spec
      (show ∃ q, C.vertices q = C.vertices p from ⟨p,rfl⟩))
  refine ⟨f,?_⟩
  intro p h a ha
  rw [hf,hf]
  exact hpoint p a ha

private theorem realizer_transport (f : ∀ x : V, X (D.vertexSort x))
    {a b c d : V} (ha : a = c) (hb : b = d)
    (hreal : ∀ h atom, D.edge a b h = some atom →
      S.colour (f a) (f b) = some atom) :
    ∀ h atom, D.edge c d h = some atom →
      S.colour (f c) (f d) = some atom := by
  cases ha
  cases hb
  exact hreal

/-- The original simple-cycle hypothesis realizes every literal edge of
every graph-theoretic simple closed walk at one common typed assignment. -/
theorem walkCycle_global
    (cycles : ∀ C : SimpleCycle D, CycleHom C)
    {x : V} (p : (graph D).Walk x x) (hp : p.IsCycle) :
    ∃ f : ∀ x : V, X (D.vertexSort x),
      ∀ (n : ℕ) (hn : n < p.length) h a,
        D.edge (p.getVert n) (p.getVert (n+1)) h = some a →
          S.colour (f (p.getVert n)) (f (p.getVert (n+1))) = some a := by
  let C := walkSimpleCycle D p hp
  obtain ⟨f,hf⟩ := cycleHom_global D (cycles C)
  refine ⟨f,?_⟩
  intro n hn h a ha
  let i : Fin p.length := ⟨n,hn⟩
  have hnext : C.vertices (cyclicNext C.length_pos i) = p.getVert (n+1) := by
    change p.getVert ((n+1)%p.length) = _
    by_cases hh : n+1 < p.length
    · rw [Nat.mod_eq_of_lt hh]
    · have he : n+1 = p.length := by omega
      simp [he]
  have hcur : C.vertices i = p.getVert n := rfl
  exact realizer_transport D f hcur hnext (hf i) h a ha

end CCO.CloneSAP.CCO
