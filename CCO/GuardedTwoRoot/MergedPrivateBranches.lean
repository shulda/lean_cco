import CCO.GuardedTwoRoot.PrivateTwoBranchClosure

/-! Actual source A06 direct-edge normalization. Keep every non-direct
branch and ONE existing direct branch per theta. All literal roots,
positions and graph edges are unchanged. The resulting concrete system
satisfies MergedDirectBranches, so C19 has no unproved merge provider. -/

universe u v w z
namespace CCO.GuardedTwoRoot.PrivateBranchSystem
variable {Roots : Type u} {Gadgets : Type v} {Branches : Type w} {V : Type z}
variable (P : PrivateBranchSystem Roots Gadgets Branches V)
noncomputable section

/-- Choose an existing direct branch, never invent a new graph edge. -/
def directChoice (g : Gadgets) : Option Branches := by
  classical
  exact if h : ∃ b, P.owner b = g ∧ P.length b = 1 then some h.choose else none

theorem directChoice_spec {g : Gadgets} {b : Branches} (h : P.directChoice g = some b) :
    P.owner b = g ∧ P.length b = 1 := by
  classical
  unfold directChoice at h
  split at h
  next hExists =>
    have he : hExists.choose = b := Option.some.inj h
    exact he ▸ hExists.choose_spec
  next => cases h

theorem directChoice_exists (b : Branches) (hb : P.length b = 1) :
    ∃ c, P.directChoice (P.owner b) = some c ∧ P.owner c = P.owner b ∧ P.length c = 1 := by
  classical
  have hExists : ∃ c, P.owner c = P.owner b ∧ P.length c = 1 := ⟨b,rfl,hb⟩
  exact ⟨hExists.choose,by simp only [directChoice,dite_eq_left hExists],hExists.choose_spec⟩

def KeptBranch (b : Branches) : Prop :=
  P.length b ≠ 1 ∨ P.directChoice (P.owner b) = some b

/-- Every selected representative is kept in its ACTUAL owner fibre. -/
theorem choice_kept {g : Gadgets} {b : Branches} (h : P.directChoice g = some b) :
    P.KeptBranch b := by
  right
  rw [(P.directChoice_spec h).1]
  exact h

/-- Different direct IDs of the same theta have the SAME complete
length-one vertex trace. Replacing one preserves edge orientation too. -/
theorem direct_vertex_eq (b c : Branches) (hOwner : P.owner b = P.owner c)
    (hb : P.length b = 1) (hc : P.length c = 1)
    (p : Fin (P.length b + 1)) (q : Fin (P.length c + 1)) (hpq : p.val = q.val) :
    P.vertex b p = P.vertex c q := by
  have hpBound := p.isLt
  have hqBound := q.isLt
  by_cases hp0 : p.val = 0
  · have hp : p = ⟨0,Nat.succ_pos _⟩ := Fin.ext hp0
    have hq : q = ⟨0,Nat.succ_pos _⟩ := Fin.ext (hpq.symm.trans hp0)
    rw [hp,hq,P.first,P.first,hOwner]
  · have hp : p = ⟨P.length b,Nat.lt_succ_self _⟩ := Fin.ext (by change p.val = P.length b; omega)
    have hq : q = ⟨P.length c,Nat.lt_succ_self _⟩ := Fin.ext (by change q.val = P.length c; omega)
    rw [hp,hq,P.last,P.last,hOwner]

/-- Same actual specified graph, restricted only in redundant direct
branch descriptions. Every long branch is retained literally. -/
def mergeDirects : PrivateBranchSystem Roots Gadgets {b : Branches // P.KeptBranch b} V where
  root := P.root
  left := P.left
  right := P.right
  different := P.different
  owner b := P.owner b.val
  length b := P.length b.val
  positive b := P.positive b.val
  vertex b := P.vertex b.val
  first b := P.first b.val
  last b := P.last b.val
  interior_not_root b := P.interior_not_root b.val
  interiors_disjoint b c hbc := P.interiors_disjoint b.val c.val
    (fun he => hbc (Subtype.ext he))
  graph := P.graph
  edge_iff v t := by
    classical
    constructor
    · intro hEdge
      obtain ⟨b,p,q,hpq,hp,hq⟩ := (P.edge_iff v t).mp hEdge
      by_cases hb : P.length b = 1
      · obtain ⟨c,hChoice,hOwner,hc⟩ := P.directChoice_exists b hb
        let p' : Fin (P.length c + 1) := ⟨p.val,by have := p.isLt; omega⟩
        let q' : Fin (P.length c + 1) := ⟨q.val,by have := q.isLt; omega⟩
        refine ⟨⟨c,P.choice_kept hChoice⟩,p',q',hpq,?_,?_⟩
        · exact (P.direct_vertex_eq b c hOwner.symm hb hc p p' rfl).symm.trans hp
        · exact (P.direct_vertex_eq b c hOwner.symm hb hc q q' rfl).symm.trans hq
      · exact ⟨⟨b,Or.inl hb⟩,p,q,hpq,hp,hq⟩
    · rintro ⟨b,p,q,hpq,hp,hq⟩
      exact (P.edge_iff v t).mpr ⟨b.val,p,q,hpq,hp,hq⟩

/-- The actual normalization DISCHARGES source A06's merge interface. -/
theorem mergeDirects_merged : P.mergeDirects.MergedDirectBranches := by
  intro b c hOwner hb hc
  apply Subtype.ext
  have hbChoice : P.directChoice (P.owner b.val) = some b.val := by
    rcases b.property with h | h
    · exact False.elim (h hb)
    · exact h
  have hcChoice : P.directChoice (P.owner c.val) = some c.val := by
    rcases c.property with h | h
    · exact False.elim (h hc)
    · exact h
  change P.owner b.val = P.owner c.val at hOwner
  rw [hOwner] at hbChoice
  exact Option.some.inj (hbChoice.symm.trans hcChoice)

/-- The SAME specified simple cycle, with the SAME injective cyclic
vertex enumeration, in the graph preserved by direct normalization. -/
def mergeCycle (C : P.Cycle) : P.mergeDirects.Cycle where
  length := C.length
  three := C.three
  positive := C.positive
  vertex := C.vertex
  adjacent := C.adjacent

theorem mergeCycle_used (C : P.Cycle) (b : {b : Branches // P.KeptBranch b}) :
    (P.mergeCycle C).UsedBranch b ↔ C.UsedBranch b.val := Iff.rfl

theorem mergeCycle_contained (C : P.Cycle) (g : Gadgets)
    (h : (P.mergeCycle C).ContainedInTheta g) : C.ContainedInTheta g := by
  intro k
  obtain ⟨b,hOwner,p,hp⟩ := h k
  exact ⟨b.val,hOwner,p,hp⟩

/-- Literal C19 after the actual merge construction: no caller supplies
MergedDirectBranches. Both old-root endpoints and the specified cycle
remain those of the original system. -/
theorem two_kept_used_branches_contained (C : P.Cycle)
    (b c : {b : Branches // P.KeptBranch b}) (hbc : b ≠ c)
    (hOwner : P.owner b.val = P.owner c.val)
    (hb : C.UsedBranch b.val) (hc : C.UsedBranch c.val) :
    C.ContainedInTheta (P.owner b.val) := by
  apply P.mergeCycle_contained C _
  exact (P.mergeCycle C).two_used_branches_contained_of_merged_directs P.mergeDirects_merged
    b c hbc hOwner hb hc

/-- Full source-A06/C19 dichotomy with merge normalization constructed
from the actual graph. Outside the contained-theta case, each theta
contributes at most one of its retained whole branch traces. -/
theorem merged_private_theta_cycle_dichotomy (C : P.Cycle) :
    (∃ g, C.ContainedInTheta g) ∨
      (∀ b c : {b : Branches // P.KeptBranch b}, C.UsedBranch b.val → C.UsedBranch c.val →
        P.owner b.val = P.owner c.val → b = c) := by
  classical
  by_cases h : ∃ g, C.ContainedInTheta g
  · exact Or.inl h
  · refine Or.inr ?_
    intro b c hb hc hOwner
    by_contra hbc
    exact h ⟨P.owner b.val,P.two_kept_used_branches_contained C b c hbc hOwner hb hc⟩

end
end CCO.GuardedTwoRoot.PrivateBranchSystem
