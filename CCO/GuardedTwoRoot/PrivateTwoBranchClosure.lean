import CCO.GuardedTwoRoot.PrivateCycleClassification

/-! Source14 C19: two genuinely different branches of one theta close
the ENTIRE specified simple cycle inside it. The duplicate direct-edge
case is exposed by an explicit source A06 merge interface rather than
being silently inferred from different branch identifiers. -/

universe u v w z
namespace CCO.GuardedTwoRoot.PrivateBranchSystem
variable {Roots : Type u} {Gadgets : Type v} {Branches : Type w} {V : Type z}
variable (P : PrivateBranchSystem Roots Gadgets Branches V)

/-- Source A06's purely structural merge step: two length-one branches
with the same owner are one graph edge, represented by one branch ID. -/
def MergedDirectBranches : Prop :=
  ∀ b c, P.owner b = P.owner c → P.length b = 1 → P.length c = 1 → b = c

noncomputable def firstNeighbour (b : Branches) : V :=
  P.vertex b ⟨1,by have := P.positive b; omega⟩
noncomputable def lastNeighbour (b : Branches) : V :=
  P.vertex b ⟨P.length b - 1,by have := P.positive b; omega⟩

theorem firstNeighbours_ne (b c : Branches) (hbc : b ≠ c)
    (hGenuine : 1 < P.length b ∨ 1 < P.length c) :
    P.firstNeighbour b ≠ P.firstNeighbour c := by
  intro he
  change P.vertex b ⟨1,by have := P.positive b; omega⟩ =
    P.vertex c ⟨1,by have := P.positive c; omega⟩ at he
  rcases hGenuine with hb | hc
  · exact hbc (P.interior_branch_unique b c
      ⟨1,by have := P.positive b; omega⟩ ⟨1,by have := P.positive c; omega⟩
      (by change 0 < (1 : ℕ); decide) hb he)
  · exact hbc ((P.interior_branch_unique c b
      ⟨1,by have := P.positive c; omega⟩ ⟨1,by have := P.positive b; omega⟩
      (by change 0 < (1 : ℕ); decide) hc he.symm).symm)

theorem lastNeighbours_ne (b c : Branches) (hbc : b ≠ c)
    (hGenuine : 1 < P.length b ∨ 1 < P.length c) :
    P.lastNeighbour b ≠ P.lastNeighbour c := by
  intro he
  change P.vertex b ⟨P.length b - 1,by have := P.positive b; omega⟩ =
    P.vertex c ⟨P.length c - 1,by have := P.positive c; omega⟩ at he
  rcases hGenuine with hb | hc
  · exact hbc (P.interior_branch_unique b c
      ⟨P.length b - 1,by have := P.positive b; omega⟩
      ⟨P.length c - 1,by have := P.positive c; omega⟩
      (by change 0 < P.length b - 1; omega)
      (by change P.length b - 1 < P.length b; omega) he)
  · exact hbc ((P.interior_branch_unique c b
      ⟨P.length c - 1,by have := P.positive c; omega⟩
      ⟨P.length b - 1,by have := P.positive b; omega⟩
      (by change 0 < P.length c - 1; omega)
      (by change P.length c - 1 < P.length c; omega) he.symm).symm)

namespace Cycle
variable {P} (C : P.Cycle)

/-- Exact connectivity of the injectively enumerated cycle, proved by
walking modular cyclic successors from an actual initial occurrence. -/
theorem all_vertices_of_edge_closed (S : Set V) (v : V) (hOn : C.On v) (hv : v ∈ S)
    (hClosed : ∀ x ∈ S, ∀ y, C.Edge x y → y ∈ S) : ∀ k, C.vertex k ∈ S := by
  obtain ⟨start,hStart⟩ := hOn
  let idx (t : ℕ) : Fin C.length := ⟨(start.val + t) % C.length,Nat.mod_lt _ C.positive⟩
  have hAll : ∀ t, C.vertex (idx t) ∈ S := by
    intro t
    induction t with
    | zero =>
      have hidx : idx 0 = start := Fin.ext (by
        dsimp [idx]
        exact Nat.mod_eq_of_lt start.isLt)
      rw [hidx,hStart]
      exact hv
    | succ t ih =>
      have hNext : cyclicNext C.positive (idx t) = idx (t + 1) := by
        apply Fin.ext
        dsimp [idx,cyclicNext]
        simp only [Nat.mod_add_mod,Nat.add_assoc]
      apply hClosed _ ih _
      refine ⟨idx t,Or.inl ⟨rfl,?_⟩⟩
      exact congrArg C.vertex hNext
  intro k
  have hIdx : idx (C.length - start.val + k.val) = k := by
    apply Fin.ext
    dsimp [idx]
    rw [show start.val + (C.length - start.val + k.val) = C.length + k.val by
      have := start.isLt
      omega]
    simp only [Nat.add_mod,Nat.mod_self,Nat.zero_add,Nat.mod_mod,Nat.mod_eq_of_lt k.isLt]
  exact hIdx ▸ hAll (C.length - start.val + k.val)

/-- Two distinct known cycle neighbours exhaust ALL cycle incidences. -/
theorem neighbours_exhaust_of_two (v a b : V) (ha : C.Edge v a) (hb : C.Edge v b)
    (hab : a ≠ b) : ∀ t, C.Edge v t → t = a ∨ t = b := by
  obtain ⟨before,after,hne,_,_,hEx⟩ := C.neighbours v (C.edge_on ha).1
  rcases hEx a ha with ha0 | ha1 <;> rcases hEx b hb with hb0 | hb1
  · exact False.elim (hab (ha0.trans hb0.symm))
  · intro t ht
    rcases hEx t ht with ht0 | ht1
    · exact Or.inl (ht0.trans ha0.symm)
    · exact Or.inr (ht1.trans hb1.symm)
  · intro t ht
    rcases hEx t ht with ht0 | ht1
    · exact Or.inr (ht0.trans hb0.symm)
    · exact Or.inl (ht1.trans ha1.symm)
  · exact False.elim (hab (ha1.trans hb1.symm))

theorem whole_first_edge (b : Branches) (h : C.WholeBranch b) :
    C.Edge (P.root (P.left (P.owner b))) (P.firstNeighbour b) := by
  have he := h.2 ⟨0,Nat.succ_pos _⟩ ⟨1,by have := P.positive b; omega⟩
    (Or.inl rfl)
  rwa [P.first] at he

theorem whole_last_edge (b : Branches) (h : C.WholeBranch b) :
    C.Edge (P.root (P.right (P.owner b))) (P.lastNeighbour b) := by
  have he := h.2 ⟨P.length b,Nat.lt_succ_self _⟩
    ⟨P.length b - 1,by have := P.positive b; omega⟩
    (Or.inr (by
      change P.length b - 1 + 1 = P.length b
      have := P.positive b
      omega))
  rwa [P.last] at he

/-- C19's genuine two-branch case. Their union saturates both root
incidences and all private interior incidences, so cyclic connectivity
puts EVERY cycle vertex on one of these same two whole branches. -/
theorem two_genuine_whole_branches_cover_cycle (b c : Branches)
    (hbc : b ≠ c) (hOwner : P.owner b = P.owner c)
    (hGenuine : 1 < P.length b ∨ 1 < P.length c)
    (hb : C.WholeBranch b) (hc : C.WholeBranch c) :
    ∀ k, C.vertex k ∈ Set.range (P.vertex b) ∪ Set.range (P.vertex c) := by
  let S : Set V := Set.range (P.vertex b) ∪ Set.range (P.vertex c)
  have hLeftB := C.whole_first_edge b hb
  have hLeftC := C.whole_first_edge c hc
  have hRightB := C.whole_last_edge b hb
  have hRightC := C.whole_last_edge c hc
  rw [← hOwner] at hLeftC hRightC
  have hLeft := C.neighbours_exhaust_of_two _ _ _ hLeftB hLeftC
    (P.firstNeighbours_ne b c hbc hGenuine)
  have hRight := C.neighbours_exhaust_of_two _ _ _ hRightB hRightC
    (P.lastNeighbours_ne b c hbc hGenuine)
  have hTrace : ∀ d, P.owner d = P.owner b → Set.range (P.vertex d) ⊆ S →
      ∀ p : Fin (P.length d + 1), ∀ t, C.Edge (P.vertex d p) t → t ∈ S := by
    intro d hd hRange p t ht
    have hpBound := p.isLt
    by_cases hp0 : p.val = 0
    · have hp : p = ⟨0,Nat.succ_pos _⟩ := Fin.ext hp0
      rw [hp,P.first,hd] at ht
      rcases hLeft t ht with he | he
      · exact Or.inl ⟨⟨1,by have := P.positive b; omega⟩,he.symm⟩
      · exact Or.inr ⟨⟨1,by have := P.positive c; omega⟩,he.symm⟩
    · by_cases hpEnd : p.val = P.length d
      · have hp : p = ⟨P.length d,Nat.lt_succ_self _⟩ := Fin.ext hpEnd
        rw [hp,P.last,hd] at ht
        rcases hRight t ht with he | he
        · exact Or.inl ⟨⟨P.length b - 1,by have := P.positive b; omega⟩,he.symm⟩
        · exact Or.inr ⟨⟨P.length c - 1,by have := P.positive c; omega⟩,he.symm⟩
      · obtain ⟨q,_,hq⟩ := P.interior_neighbours d p (by omega) (by omega) t (C.edge_adjacent ht)
        exact hRange ⟨q,hq⟩
  apply C.all_vertices_of_edge_closed S (P.vertex b ⟨0,Nat.succ_pos _⟩)
    (hb.1 _) (Or.inl ⟨_,rfl⟩)
  intro v hv t ht
  rcases hv with ⟨p,rfl⟩ | ⟨p,rfl⟩
  · exact hTrace b rfl (fun _ h => Or.inl h) p t ht
  · exact hTrace c hOwner.symm (fun _ h => Or.inr h) p t ht

/-- Source14 C19 for any two used branches with genuinely different
traces. The conclusion covers the ENTIRE simple cycle. -/
theorem two_genuine_used_branches_contained (b c : Branches)
    (hbc : b ≠ c) (hOwner : P.owner b = P.owner c)
    (hGenuine : 1 < P.length b ∨ 1 < P.length c)
    (hb : C.UsedBranch b) (hc : C.UsedBranch c) : C.ContainedInTheta (P.owner b) := by
  intro k
  rcases C.two_genuine_whole_branches_cover_cycle b c hbc hOwner hGenuine
    (C.used_branch_whole b hb) (C.used_branch_whole c hc) k with ⟨p,hp⟩ | ⟨p,hp⟩
  · exact ⟨b,rfl,p,hp⟩
  · exact ⟨c,hOwner.symm,p,hp⟩

/-- The ordinary A06 merged-direct case discharges the only missing
genuine-trace condition. Without this merge interface, two different IDs
may describe the same direct edge and the stronger assertion is false. -/
theorem two_used_branches_contained_of_merged_directs (hMerged : P.MergedDirectBranches)
    (b c : Branches) (hbc : b ≠ c) (hOwner : P.owner b = P.owner c)
    (hb : C.UsedBranch b) (hc : C.UsedBranch c) : C.ContainedInTheta (P.owner b) := by
  apply C.two_genuine_used_branches_contained b c hbc hOwner _ hb hc
  by_contra h
  have hbPos := P.positive b
  have hcPos := P.positive c
  have hbOne : P.length b = 1 := by omega
  have hcOne : P.length c = 1 := by omega
  exact hbc (hMerged b c hOwner hbOne hcOne)

/-- Outside a particular theta, a simple cycle uses at most ONE of
its merged branch traces. Thus returning along a second genuine branch
forces the entire cycle into that theta, exactly source14 C19. -/
theorem used_branch_unique_outside_theta (hMerged : P.MergedDirectBranches)
    (b c : Branches) (hOwner : P.owner b = P.owner c)
    (hb : C.UsedBranch b) (hc : C.UsedBranch c)
    (hOutside : ¬ C.ContainedInTheta (P.owner b)) : b = c := by
  by_contra hbc
  exact hOutside (C.two_used_branches_contained_of_merged_directs hMerged b c hbc hOwner hb hc)

/-- Nontrivial source cycle dichotomy: either one theta contains the
ENTIRE cycle, or each theta contributes at most one merged whole branch. -/
theorem private_theta_cycle_dichotomy (hMerged : P.MergedDirectBranches) :
    (∃ g, C.ContainedInTheta g) ∨
      (∀ b c, C.UsedBranch b → C.UsedBranch c → P.owner b = P.owner c → b = c) := by
  classical
  by_cases h : ∃ g, C.ContainedInTheta g
  · exact Or.inl h
  · refine Or.inr ?_
    intro b c hb hc hOwner
    exact C.used_branch_unique_outside_theta hMerged b c hOwner hb hc
      (fun hg => h ⟨P.owner b,hg⟩)

end Cycle
end CCO.GuardedTwoRoot.PrivateBranchSystem
