import CCO.GuardedTwoRoot.PrivateBranches

/-! Every touched private branch is traversed WHOLE, including its
literal OLD roots. Direct edges are positive length-one branches. Used
branch identifiers are retained on contraction, so parallel macro sides
are allowed and no simple-graph macro-cycle claim is made. -/

universe u v w z
namespace CCO.GuardedTwoRoot.PrivateBranchSystem.Cycle
variable {Roots : Type u} {Gadgets : Type v} {Branches : Type w} {V : Type z}
variable {P : PrivateBranchSystem Roots Gadgets Branches V} (C : P.Cycle)

def WholeBranch (b : Branches) : Prop :=
  (∀ p : Fin (P.length b + 1), C.On (P.vertex b p)) ∧
  ∀ p q : Fin (P.length b + 1), P.PositionAdjacent b p q →
    C.Edge (P.vertex b p) (P.vertex b q)

/-- C18/C20: touching one strict interior forces every original position
and every path edge onto this SAME specified simple cycle. -/
theorem whole_branch_of_interior (b : Branches) (p : Fin (P.length b + 1))
    (hp0 : 0 < p.val) (hpEnd : p.val < P.length b) (hOn : C.On (P.vertex b p)) :
    C.WholeBranch b := by
  have hpBound := p.isLt
  have hDown : ∀ d : ℕ, ∀ hd : d ≤ p.val,
      C.On (P.vertex b ⟨p.val - d,by omega⟩) := by
    intro d
    induction d with
    | zero => intro hd; simpa only [Nat.sub_zero] using hOn
    | succ d ih =>
      intro hd
      let current : Fin (P.length b + 1) := ⟨p.val - d,by omega⟩
      let next : Fin (P.length b + 1) := ⟨p.val - (d + 1),by omega⟩
      have hCurrent : C.On (P.vertex b current) := ih (by omega)
      have hEdge := C.interior_cycle_edge b current
        (by dsimp [current]; omega) (by dsimp [current]; omega) hCurrent next
        (Or.inr (by dsimp [current,next]; omega))
      exact (C.edge_on hEdge).2
  have hUp : ∀ d : ℕ, ∀ hd : p.val + d ≤ P.length b,
      C.On (P.vertex b ⟨p.val + d,by omega⟩) := by
    intro d
    induction d with
    | zero => intro hd; simpa only [Nat.add_zero] using hOn
    | succ d ih =>
      intro hd
      let current : Fin (P.length b + 1) := ⟨p.val + d,by omega⟩
      let next : Fin (P.length b + 1) := ⟨p.val + (d + 1),by omega⟩
      have hCurrent : C.On (P.vertex b current) := ih (by omega)
      have hEdge := C.interior_cycle_edge b current
        (by dsimp [current]; omega) (by dsimp [current]; omega) hCurrent next
        (Or.inl (by dsimp [current,next]; omega))
      exact (C.edge_on hEdge).2
  have hAll : ∀ q : Fin (P.length b + 1), C.On (P.vertex b q) := by
    intro q
    have hqBound := q.isLt
    by_cases hqp : q.val ≤ p.val
    · have h := hDown (p.val - q.val) (by omega)
      have hv : p.val - (p.val - q.val) = q.val := by omega
      have he : (⟨p.val - (p.val - q.val),by omega⟩ : Fin (P.length b + 1)) = q :=
        Fin.ext hv
      exact he ▸ h
    · have h := hUp (q.val - p.val) (by omega)
      have hv : p.val + (q.val - p.val) = q.val := by omega
      have he : (⟨p.val + (q.val - p.val),by omega⟩ : Fin (P.length b + 1)) = q :=
        Fin.ext hv
      exact he ▸ h
  refine ⟨hAll,?_⟩
  intro q r hqr
  have hqBound := q.isLt
  have hrBound := r.isLt
  by_cases hq0 : q.val = 0
  · have hr0 : 0 < r.val := by rcases hqr with h | h <;> omega
    have hrEnd : r.val < P.length b := by rcases hqr with h | h <;> omega
    exact (C.edge_symm _ _).mpr (C.interior_cycle_edge b r hr0 hrEnd (hAll r) q
      ((P.positionAdjacent_symm b q r).mp hqr))
  · by_cases hqEnd : q.val = P.length b
    · have hr0 : 0 < r.val := by rcases hqr with h | h <;> omega
      have hrEnd : r.val < P.length b := by rcases hqr with h | h <;> omega
      exact (C.edge_symm _ _).mpr (C.interior_cycle_edge b r hr0 hrEnd (hAll r) q
        ((P.positionAdjacent_symm b q r).mp hqr))
    · exact C.interior_cycle_edge b q (by omega) (by omega) (hAll q) r hqr

/-- The direct branch case has no private position to propagate through:
its one actual graph edge is already the whole positive path. -/
theorem direct_branch_whole (b : Branches) (hLength : P.length b = 1)
    (p q : Fin (P.length b + 1)) (hpq : P.PositionAdjacent b p q)
    (hEdge : C.Edge (P.vertex b p) (P.vertex b q)) : C.WholeBranch b := by
  have hpBound := p.isLt
  have hqBound := q.isLt
  have hEnds : ∀ r : Fin (P.length b + 1), r = p ∨ r = q := by
    intro r
    have hrBound := r.isLt
    rcases hpq with h | h
    · by_cases he : r.val = p.val
      · exact Or.inl (Fin.ext he)
      · exact Or.inr (Fin.ext (by omega))
    · by_cases he : r.val = p.val
      · exact Or.inl (Fin.ext he)
      · exact Or.inr (Fin.ext (by omega))
  refine ⟨?_,?_⟩
  · intro r
    rcases hEnds r with rfl | rfl
    · exact (C.edge_on hEdge).1
    · exact (C.edge_on hEdge).2
  · intro r s hrs
    have hrsNe : r ≠ s := by intro he; subst s; rcases hrs with h | h <;> omega
    rcases hEnds r with rfl | rfl <;> rcases hEnds s with rfl | rfl
    · exact False.elim (hrsNe rfl)
    · exact hEdge
    · exact (C.edge_symm _ _).mp hEdge
    · exact False.elim (hrsNe rfl)

/-- EVERY used branch, including a direct root edge, is a complete
traversal. The conclusion refers to actual cycle edges, not merely an
ambient path whose vertices happen to meet the cycle. -/
theorem whole_branch_of_edge (b : Branches) (p q : Fin (P.length b + 1))
    (hpq : P.PositionAdjacent b p q)
    (hEdge : C.Edge (P.vertex b p) (P.vertex b q)) : C.WholeBranch b := by
  have hpBound := p.isLt
  have hqBound := q.isLt
  by_cases hLength : P.length b = 1
  · exact C.direct_branch_whole b hLength p q hpq hEdge
  · have hLong : 1 < P.length b := by have := P.positive b; omega
    by_cases hp0 : p.val = 0
    · have hq0 : 0 < q.val := by rcases hpq with h | h <;> omega
      have hqEnd : q.val < P.length b := by rcases hpq with h | h <;> omega
      exact C.whole_branch_of_interior b q hq0 hqEnd (C.edge_on hEdge).2
    · by_cases hpEnd : p.val = P.length b
      · have hq0 : 0 < q.val := by rcases hpq with h | h <;> omega
        have hqEnd : q.val < P.length b := by rcases hpq with h | h <;> omega
        exact C.whole_branch_of_interior b q hq0 hqEnd (C.edge_on hEdge).2
      · exact C.whole_branch_of_interior b p (by omega) (by omega) (C.edge_on hEdge).1

def UsedBranch (b : Branches) : Prop :=
  ∃ p q : Fin (P.length b + 1), P.PositionAdjacent b p q ∧
    C.Edge (P.vertex b p) (P.vertex b q)

theorem used_branch_whole (b : Branches) (h : C.UsedBranch b) : C.WholeBranch b := by
  obtain ⟨p,q,hpq,hEdge⟩ := h
  exact C.whole_branch_of_edge b p q hpq hEdge

/-- C21: contraction retains BOTH literal OLD root endpoints. In
particular it does not use a completion colour on any unrecorded pair. -/
theorem used_branch_old_endpoints (b : Branches) (h : C.UsedBranch b) :
    C.On (P.root (P.left (P.owner b))) ∧ C.On (P.root (P.right (P.owner b))) := by
  have hw := (C.used_branch_whole b h).1
  exact ⟨P.first b ▸ hw ⟨0,Nat.succ_pos _⟩,
    P.last b ▸ hw ⟨P.length b,Nat.lt_succ_self _⟩⟩

/-- Every traversed graph edge has an actual whole-branch witness. -/
theorem edge_covered_by_whole_branch {v w : V} (h : C.Edge v w) :
    ∃ (b : Branches) (p q : Fin (P.length b + 1)), P.PositionAdjacent b p q ∧
      P.vertex b p = v ∧ P.vertex b q = w ∧ C.WholeBranch b := by
  obtain ⟨b,p,q,hpq,hp,hq⟩ := (P.edge_iff _ _).mp (C.edge_adjacent h)
  refine ⟨b,p,q,hpq,hp,hq,?_⟩
  apply C.whole_branch_of_edge b p q hpq
  rwa [hp,hq]

/-- The macro-side type retains occurrence identities. Different sides
may have the same old endpoint pair, so parallel macro sides are legal. -/
abbrev MacroSide := {b : Branches // C.UsedBranch b}

def macroLeft (b : C.MacroSide) : Roots := P.left (P.owner b.val)
def macroRight (b : C.MacroSide) : Roots := P.right (P.owner b.val)

theorem macro_side_old (b : C.MacroSide) :
    C.macroLeft b ≠ C.macroRight b ∧
      C.On (P.root (C.macroLeft b)) ∧ C.On (P.root (C.macroRight b)) :=
  ⟨P.different _,C.used_branch_old_endpoints b.val b.property⟩

/-- Source private-theta traversal conclusion, with no semantic source
assumption and no assertion of simple-graph simplicity after contraction. -/
theorem typed_private_theta_cycle :
    (∀ b, C.UsedBranch b → C.WholeBranch b) ∧
    (∀ b : C.MacroSide, C.macroLeft b ≠ C.macroRight b ∧
      C.On (P.root (C.macroLeft b)) ∧ C.On (P.root (C.macroRight b))) :=
  ⟨C.used_branch_whole,C.macro_side_old⟩

end CCO.GuardedTwoRoot.PrivateBranchSystem.Cycle
