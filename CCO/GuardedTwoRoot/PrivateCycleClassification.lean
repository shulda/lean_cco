import CCO.GuardedTwoRoot.PrivateCycles

/-! Pure source14 cycle classification. An actual edge-by-edge
branch certificate is selected from the SPECIFIED simple cycle. Branch
changes occur only at literal OLD roots. Root occurrences are injective,
so root-only cycles and length-one branches are retained, and no claim
that the contracted multigraph is a simple graph is made. -/

universe u v w z
namespace CCO.GuardedTwoRoot.PrivateBranchSystem
variable {Roots : Type u} {Gadgets : Type v} {Branches : Type w} {V : Type z}
variable (P : PrivateBranchSystem Roots Gadgets Branches V)

/-- Strictly private positions determine their ACTUAL branch uniquely,
including against the endpoints of every other branch. -/
theorem interior_branch_unique (b c : Branches)
    (p : Fin (P.length b + 1)) (q : Fin (P.length c + 1))
    (hp0 : 0 < p.val) (hpEnd : p.val < P.length b)
    (he : P.vertex b p = P.vertex c q) : b = c := by
  by_contra hbc
  have hqBound := q.isLt
  by_cases hq0 : q.val = 0
  · have hq : q = ⟨0,Nat.succ_pos _⟩ := Fin.ext hq0
    rw [hq,P.first] at he
    exact P.interior_not_root b p hp0 hpEnd _ he
  · by_cases hqEnd : q.val = P.length c
    · have hq : q = ⟨P.length c,Nat.lt_succ_self _⟩ := Fin.ext hqEnd
      rw [hq,P.last] at he
      exact P.interior_not_root b p hp0 hpEnd _ he
    · exact P.interiors_disjoint b c hbc p q hp0 hpEnd (by omega) (by omega) he

theorem branch_vertex_root_iff (b : Branches) (p : Fin (P.length b + 1)) :
    (∃ r, P.vertex b p = P.root r) ↔ p.val = 0 ∨ p.val = P.length b := by
  constructor
  · rintro ⟨r,hr⟩
    have hp := p.isLt
    by_cases h0 : p.val = 0
    · exact Or.inl h0
    · by_cases hEnd : p.val = P.length b
      · exact Or.inr hEnd
      · exact False.elim (P.interior_not_root b p (by omega) (by omega) r hr)
  · rintro (h0 | hEnd)
    · have hp : p = ⟨0,Nat.succ_pos _⟩ := Fin.ext h0
      exact ⟨P.left (P.owner b),hp ▸ P.first b⟩
    · have hp : p = ⟨P.length b,Nat.lt_succ_self _⟩ := Fin.ext hEnd
      exact ⟨P.right (P.owner b),hp ▸ P.last b⟩

theorem root_at_branch_endpoint (b : Branches) (p : Fin (P.length b + 1))
    (r : Roots) (he : P.vertex b p = P.root r) :
    r = P.left (P.owner b) ∨ r = P.right (P.owner b) := by
  rcases (P.branch_vertex_root_iff b p).mp ⟨r,he⟩ with h0 | hEnd
  · left
    have hp : p = ⟨0,Nat.succ_pos _⟩ := Fin.ext h0
    rw [hp,P.first] at he
    exact P.root.injective he.symm
  · right
    have hp : p = ⟨P.length b,Nat.lt_succ_self _⟩ := Fin.ext hEnd
    rw [hp,P.last] at he
    exact P.root.injective he.symm

/-- A meeting of different branch identifiers is necessarily an OLD
root, including possible repeated direct-edge descriptions. -/
theorem different_branches_meet_at_old_root (b c : Branches) (hbc : b ≠ c)
    (p : Fin (P.length b + 1)) (q : Fin (P.length c + 1))
    (he : P.vertex b p = P.vertex c q) :
    ∃ r, P.root r = P.vertex b p ∧
      (r = P.left (P.owner b) ∨ r = P.right (P.owner b)) ∧
      (r = P.left (P.owner c) ∨ r = P.right (P.owner c)) := by
  have hp := p.isLt
  have hEnd : p.val = 0 ∨ p.val = P.length b := by
    by_contra hn
    have hn0 : p.val ≠ 0 := fun h => hn (Or.inl h)
    have hnEnd : p.val ≠ P.length b := fun h => hn (Or.inr h)
    exact hbc (P.interior_branch_unique b c p q (by omega) (by omega) he)
  obtain ⟨r,hr⟩ := (P.branch_vertex_root_iff b p).mpr hEnd
  exact ⟨r,hr.symm,P.root_at_branch_endpoint b p r hr,
    P.root_at_branch_endpoint c q r (he.symm.trans hr)⟩

/-- The actual whole positive branch containing one oriented graph edge. -/
structure BranchEdgeWitness (v w : V) where
  branch : Branches
  source : Fin (P.length branch + 1)
  target : Fin (P.length branch + 1)
  adjacent : P.PositionAdjacent branch source target
  source_eq : P.vertex branch source = v
  target_eq : P.vertex branch target = w

theorem branch_edge_witness {v w : V} (h : P.graph.Adj v w) :
    Nonempty (P.BranchEdgeWitness v w) := by
  obtain ⟨b,p,q,hpq,hp,hq⟩ := (P.edge_iff v w).mp h
  exact ⟨⟨b,p,q,hpq,hp,hq⟩⟩

namespace Cycle
variable {P} (C : P.Cycle)

noncomputable def cycleEdge (k : Fin C.length) :
    P.BranchEdgeWitness (C.vertex k) (C.vertex (cyclicNext C.positive k)) :=
  (P.branch_edge_witness (C.adjacent k)).some

theorem cycleEdge_used (k : Fin C.length) : C.UsedBranch (C.cycleEdge k).branch := by
  refine ⟨(C.cycleEdge k).source,(C.cycleEdge k).target,(C.cycleEdge k).adjacent,?_⟩
  rw [(C.cycleEdge k).source_eq,(C.cycleEdge k).target_eq]
  exact ⟨k,Or.inl ⟨rfl,rfl⟩⟩

theorem cycleEdge_whole (k : Fin C.length) : C.WholeBranch (C.cycleEdge k).branch :=
  C.used_branch_whole _ (C.cycleEdge_used k)

/-- EVERY actual change of traversed branch has a literal old source
root at the shared cycle vertex. Both macro-side incidences are retained. -/
theorem branch_change_old_root (k : Fin C.length)
    (hChange : (C.cycleEdge k).branch ≠
      (C.cycleEdge (cyclicNext C.positive k)).branch) :
    ∃ r, P.root r = C.vertex (cyclicNext C.positive k) ∧
      (r = P.left (P.owner (C.cycleEdge k).branch) ∨
        r = P.right (P.owner (C.cycleEdge k).branch)) ∧
      (r = P.left (P.owner (C.cycleEdge (cyclicNext C.positive k)).branch) ∨
        r = P.right (P.owner (C.cycleEdge (cyclicNext C.positive k)).branch)) := by
  obtain ⟨r,hr,hFirst,hSecond⟩ := P.different_branches_meet_at_old_root
    (C.cycleEdge k).branch (C.cycleEdge (cyclicNext C.positive k)).branch hChange
    (C.cycleEdge k).target (C.cycleEdge (cyclicNext C.positive k)).source
    ((C.cycleEdge k).target_eq.trans (C.cycleEdge (cyclicNext C.positive k)).source_eq.symm)
  exact ⟨r,hr.trans (C.cycleEdge k).target_eq,hFirst,hSecond⟩

/-- Root occurrences, not quotient identifications of macro edges. -/
abbrev OldRootIndex := {k : Fin C.length // ∃ r, P.root r = C.vertex k}

noncomputable def oldRootAt (k : C.OldRootIndex) : Roots := k.property.choose

theorem oldRootAt_eq (k : C.OldRootIndex) : P.root (C.oldRootAt k) = C.vertex k.val :=
  k.property.choose_spec

/-- No original root can occur twice in the contracted cyclic sequence.
This does not discard parallel macro sides between two distinct roots. -/
theorem oldRootAt_injective : Function.Injective C.oldRootAt := by
  intro a b he
  apply Subtype.ext
  apply C.vertex.injective
  exact (C.oldRootAt_eq a).symm.trans
    ((congrArg P.root he).trans (C.oldRootAt_eq b))

/-- Every specified simple cycle has at least TWO distinct old roots.
The conclusion also covers cycles consisting entirely of direct root edges. -/
theorem cycle_has_two_old_roots :
    ∃ r s : Roots, r ≠ s ∧ C.On (P.root r) ∧ C.On (P.root s) := by
  let k : Fin C.length := ⟨0,C.positive⟩
  let b := (C.cycleEdge k).branch
  exact ⟨P.left (P.owner b),P.right (P.owner b),P.different _,
    C.used_branch_old_endpoints b (C.cycleEdge_used k)⟩

/-- Vertices of one theta retain their actual branch occurrence. -/
def InTheta (g : Gadgets) (v : V) : Prop :=
  ∃ b : Branches, P.owner b = g ∧ ∃ p, P.vertex b p = v

def ContainedInTheta (g : Gadgets) : Prop := ∀ k, InTheta (P := P) g (C.vertex k)

/-- Source14 classification with an explicit contraction certificate.
Outside the single-theta case, every specified edge lies on a WHOLE
positive old-root-to-old-root branch, and branch changes occur ONLY at
old roots. Actual old root occurrences are injective. No completion
colours, semantic source assumptions or synthetic macro loops are used. -/
theorem private_theta_cycle_classification :
    (∃ g, C.ContainedInTheta g) ∨
      ((¬ ∃ g, C.ContainedInTheta g) ∧
        (∀ k, C.WholeBranch (C.cycleEdge k).branch) ∧
        (∀ k, (C.cycleEdge k).branch ≠ (C.cycleEdge (cyclicNext C.positive k)).branch →
          ∃ r, P.root r = C.vertex (cyclicNext C.positive k)) ∧
        Function.Injective C.oldRootAt) := by
  classical
  by_cases h : ∃ g, C.ContainedInTheta g
  · exact Or.inl h
  · refine Or.inr ⟨h,C.cycleEdge_whole,?_,C.oldRootAt_injective⟩
    intro k hk
    obtain ⟨r,hr,_,_⟩ := C.branch_change_old_root k hk
    exact ⟨r,hr⟩

end Cycle
end CCO.GuardedTwoRoot.PrivateBranchSystem
