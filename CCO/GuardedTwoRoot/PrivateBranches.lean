import CCO.RawExact.SimpleCycleDegreeTwo
import Mathlib.Combinatorics.SimpleGraph.Basic

/-! Pure private-path geometry. Roots are fixed OLD vertices; a branch
has positive length, injective positions, and strict interiors private
across the entire network. Every specified edge is one path step. There
are no original-source, action, SAP, CCO or hidden-structure hypotheses. -/

universe u v w z
namespace CCO.GuardedTwoRoot

structure PrivateBranchSystem (Roots : Type u) (Gadgets : Type v)
    (Branches : Type w) (V : Type z) where
  root : Roots ↪ V
  left : Gadgets → Roots
  right : Gadgets → Roots
  different : ∀ g, left g ≠ right g
  owner : Branches → Gadgets
  length : Branches → ℕ
  positive : ∀ b, 0 < length b
  vertex : ∀ b, Fin (length b + 1) ↪ V
  first : ∀ b, vertex b ⟨0,Nat.succ_pos _⟩ = root (left (owner b))
  last : ∀ b, vertex b ⟨length b,Nat.lt_succ_self _⟩ = root (right (owner b))
  interior_not_root : ∀ b (p : Fin (length b + 1)), 0 < p.val → p.val < length b →
    ∀ r, vertex b p ≠ root r
  interiors_disjoint : ∀ b c, b ≠ c → ∀ (p : Fin (length b + 1))
    (q : Fin (length c + 1)), 0 < p.val → p.val < length b →
      0 < q.val → q.val < length c → vertex b p ≠ vertex c q
  graph : SimpleGraph V
  edge_iff : ∀ x y, graph.Adj x y ↔
    ∃ (b : Branches) (p q : Fin (length b + 1)),
      (p.val + 1 = q.val ∨ q.val + 1 = p.val) ∧ vertex b p = x ∧ vertex b q = y

namespace PrivateBranchSystem
variable {Roots : Type u} {Gadgets : Type v} {Branches : Type w} {V : Type z}
variable (P : PrivateBranchSystem Roots Gadgets Branches V)

def PositionAdjacent (b : Branches) (p q : Fin (P.length b + 1)) : Prop :=
  p.val + 1 = q.val ∨ q.val + 1 = p.val

theorem positionAdjacent_symm (b : Branches) (p q : Fin (P.length b + 1)) :
    P.PositionAdjacent b p q ↔ P.PositionAdjacent b q p := or_comm

theorem branch_step (b : Branches) (p q : Fin (P.length b + 1))
    (h : P.PositionAdjacent b p q) : P.graph.Adj (P.vertex b p) (P.vertex b q) :=
  (P.edge_iff _ _).mpr ⟨b,p,q,h,rfl,rfl⟩

/-- C18: every possible incident edge of an interior is in that SAME
branch. In particular a cycle cannot jump to another private gadget. -/
theorem interior_neighbours (b : Branches) (p : Fin (P.length b + 1))
    (hp0 : 0 < p.val) (hpEnd : p.val < P.length b) (v : V)
    (h : P.graph.Adj (P.vertex b p) v) :
    ∃ q : Fin (P.length b + 1), P.PositionAdjacent b p q ∧ P.vertex b q = v := by
  obtain ⟨c,q,r,hqr,hq,hr⟩ := (P.edge_iff _ _).mp h
  have hcb : c = b := by
    by_contra hne
    have hqBound := q.isLt
    by_cases hq0 : q.val = 0
    · have hq' : q = ⟨0,Nat.succ_pos _⟩ := Fin.ext hq0
      rw [hq',P.first] at hq
      exact P.interior_not_root b p hp0 hpEnd _ hq.symm
    · by_cases hqEnd : q.val = P.length c
      · have hq' : q = ⟨P.length c,Nat.lt_succ_self _⟩ := Fin.ext hqEnd
        rw [hq',P.last] at hq
        exact P.interior_not_root b p hp0 hpEnd _ hq.symm
      · exact P.interiors_disjoint b c (Ne.symm hne) p q hp0 hpEnd
          (by omega) (by omega) hq.symm
  subst c
  have he : q = p := (P.vertex b).injective hq
  subst q
  exact ⟨r,hqr,hr⟩

/-- The precise two possible neighbours of one strict interior. -/
theorem interior_neighbours_exhaust (b : Branches) (p : Fin (P.length b + 1))
    (hp0 : 0 < p.val) (hpEnd : p.val < P.length b) :
    ∀ v, P.graph.Adj (P.vertex b p) v →
      v = P.vertex b ⟨p.val - 1,by omega⟩ ∨
      v = P.vertex b ⟨p.val + 1,by omega⟩ := by
  intro v hv
  obtain ⟨q,hq,rfl⟩ := P.interior_neighbours b p hp0 hpEnd v hv
  rcases hq with hq | hq
  · right
    have he : q.val = p.val + 1 := hq.symm
    exact congrArg (P.vertex b) (show q = ⟨p.val + 1,by omega⟩ from Fin.ext he)
  · left
    have he : q.val = p.val - 1 := by omega
    exact congrArg (P.vertex b) (show q = ⟨p.val - 1,by omega⟩ from Fin.ext he)

/-- A simple cycle is only a finite injective cyclic enumeration in
the specified graph. Parallel macro sides are deliberately not identified. -/
structure Cycle where
  length : ℕ
  three : 3 ≤ length
  positive : 0 < length
  vertex : Fin length ↪ V
  adjacent : ∀ k, P.graph.Adj (vertex k) (vertex (cyclicNext positive k))

namespace Cycle
variable {P} (C : P.Cycle)

def On (v : V) : Prop := ∃ k, C.vertex k = v

def Edge (v w : V) : Prop := ∃ k,
  (C.vertex k = v ∧ C.vertex (cyclicNext C.positive k) = w) ∨
  (C.vertex k = w ∧ C.vertex (cyclicNext C.positive k) = v)

theorem edge_symm (v w : V) : C.Edge v w ↔ C.Edge w v := by
  constructor <;> rintro ⟨k,h | h⟩
  · exact ⟨k,Or.inr h⟩
  · exact ⟨k,Or.inl h⟩
  · exact ⟨k,Or.inr h⟩
  · exact ⟨k,Or.inl h⟩

theorem edge_on {v w : V} (h : C.Edge v w) : C.On v ∧ C.On w := by
  obtain ⟨k,h | h⟩ := h
  · exact ⟨⟨k,h.1⟩,⟨cyclicNext C.positive k,h.2⟩⟩
  · exact ⟨⟨cyclicNext C.positive k,h.2⟩,⟨k,h.1⟩⟩

theorem edge_adjacent {v w : V} (h : C.Edge v w) : P.graph.Adj v w := by
  obtain ⟨k,h | h⟩ := h
  · rw [← h.1,← h.2]
    exact C.adjacent k
  · rw [← h.1,← h.2]
    exact (C.adjacent k).symm

/-- Exactly two distinct actual traversed neighbours at a cycle vertex. -/
theorem neighbours (v : V) (hOn : C.On v) :
    ∃ before after : V, before ≠ after ∧ C.Edge v before ∧ C.Edge v after ∧
      ∀ w, C.Edge v w → w = before ∨ w = after := by
  obtain ⟨p,hp⟩ := hOn
  obtain ⟨prev,hprev⟩ := RawExact.cyclicNext_surjective C.positive p
  refine ⟨C.vertex prev,C.vertex (cyclicNext C.positive p),?_,?_,?_,?_⟩
  · intro h
    have he := C.vertex.injective h
    exact RawExact.cyclicNext_no_two_cycle C.positive C.three p prev he.symm hprev
  · exact ⟨prev,Or.inr ⟨rfl,(congrArg C.vertex hprev).trans hp⟩⟩
  · exact ⟨p,Or.inl ⟨hp,rfl⟩⟩
  · rintro w ⟨k,h | h⟩
    · have hk : k = p := C.vertex.injective (h.1.trans hp.symm)
      subst k
      exact Or.inr h.2.symm
    · have hk : k = prev := RawExact.cyclicNext_injective C.positive
        ((C.vertex.injective (h.2.trans hp.symm)).trans hprev.symm)
      subst k
      exact Or.inl h.1.symm

theorem degree_two_edges (v a b : V)
    (hExhaust : ∀ w, P.graph.Adj v w → w = a ∨ w = b) (hOn : C.On v) :
    C.Edge v a ∧ C.Edge v b := by
  obtain ⟨before,after,hne,hBefore,hAfter,_⟩ := C.neighbours v hOn
  rcases hExhaust before (C.edge_adjacent hBefore) with hba | hbb <;>
    rcases hExhaust after (C.edge_adjacent hAfter) with haa | hab
  · exact False.elim (hne (hba.trans haa.symm))
  · exact ⟨hba ▸ hBefore,hab ▸ hAfter⟩
  · exact ⟨haa ▸ hAfter,hbb ▸ hBefore⟩
  · exact False.elim (hne (hbb.trans hab.symm))

theorem interior_cycle_edge (b : Branches) (p : Fin (P.length b + 1))
    (hp0 : 0 < p.val) (hpEnd : p.val < P.length b) (hOn : C.On (P.vertex b p))
    (q : Fin (P.length b + 1)) (hpq : P.PositionAdjacent b p q) :
    C.Edge (P.vertex b p) (P.vertex b q) := by
  have hEdges := C.degree_two_edges (P.vertex b p)
    (P.vertex b ⟨p.val - 1,by omega⟩) (P.vertex b ⟨p.val + 1,by omega⟩)
    (P.interior_neighbours_exhaust b p hp0 hpEnd) hOn
  rcases hpq with hq | hq
  · have hv : q.val = p.val + 1 := hq.symm
    have he : q = ⟨p.val + 1,by omega⟩ := Fin.ext hv
    exact he ▸ hEdges.2
  · have hv : q.val = p.val - 1 := by omega
    have he : q = ⟨p.val - 1,by omega⟩ := Fin.ext hv
    exact he ▸ hEdges.1

end Cycle
end PrivateBranchSystem
end CCO.GuardedTwoRoot
