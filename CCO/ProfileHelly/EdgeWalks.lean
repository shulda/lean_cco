import CCO.ProfileHelly.Fill

/-! Moving a recorded walk to another network on the same vertices while
retaining ALL its actual edge labels. No ambient source is used. -/
universe u v z
namespace CCO.ProfileHelly.Network
variable {ι : Type u} {T : Table.{u,v} ι} {V : Type z} {sort : V → ι}
variable (D E : Network T sort)
open SimpleGraph

noncomputable def transferWalk : {x y : V} → (p : E.graph.Walk x y) →
    (∀ {a b}, s(a,b) ∈ p.edges → E.edge a b = D.edge a b) → D.graph.Walk x y
  | _,_,.nil,_ => .nil
  | _,_,.cons h p,hp => .cons
      (by
        obtain ⟨a,ha⟩ := h
        exact ⟨a,(hp (List.Mem.head _)).symm.trans ha⟩)
      (transferWalk p (fun h => hp (List.Mem.tail _ h)))

theorem transferWalk_support {x y : V} (p : E.graph.Walk x y) (hp) :
    (D.transferWalk E p hp).support = p.support := by
  induction p with
  | nil => rfl
  | cons h p ih => exact congrArg (_ :: ·) (ih _)

theorem transferWalk_edges {x y : V} (p : E.graph.Walk x y) (hp) :
    (D.transferWalk E p hp).edges = p.edges := by
  induction p with
  | nil => rfl
  | cons h p ih => exact congrArg (_ :: ·) (ih _)

theorem transferWalk_length {x y : V} (p : E.graph.Walk x y) (hp) :
    (D.transferWalk E p hp).length = p.length := by
  induction p with
  | nil => rfl
  | cons h p ih => exact congrArg (· + 1) (ih _)

theorem transferWalk_not_nil {x y : V} (p : E.graph.Walk x y) (hp) (hn : ¬p.Nil) :
    ¬(D.transferWalk E p hp).Nil := by
  rw [← Walk.length_eq_zero_iff,D.transferWalk_length,Walk.length_eq_zero_iff]
  exact hn

theorem transferWalk_isPath {x y : V} (p : E.graph.Walk x y) (hp) (hn : p.IsPath) :
    (D.transferWalk E p hp).IsPath := by
  simpa only [Walk.isPath_def,D.transferWalk_support] using hn

theorem transferWalk_word {x y : V} (p : E.graph.Walk x y) (hp) (hn : ¬p.Nil) :
    D.walkWord (D.transferWalk E p hp) (D.transferWalk_not_nil E p hp hn) = E.walkWord p hn := by
  induction p with
  | nil => exact False.elim (hn .nil)
  | @cons x y z h p ih =>
    let h' : D.graph.Adj x y := ⟨E.label h,(hp (List.Mem.head _)).symm.trans (E.label_spec h)⟩
    have hl : D.label h' = E.label h := D.label_unique h' _
      ((hp (List.Mem.head _)).symm.trans (E.label_spec h))
    cases p with
    | nil => exact congrArg Word.single hl
    | cons k p =>
      change Word.cons (D.label h') _ = Word.cons (E.label h) _
      rw [hl]
      exact congrArg (Word.cons (E.label h)) (ih (fun h => hp (List.Mem.tail _ h)) Walk.not_nil_cons)

theorem transferWalk_profile {x y : V} (p : E.graph.Walk x y) (hp) (hn : ¬p.Nil) :
    D.walkProfile (D.transferWalk E p hp) (D.transferWalk_not_nil E p hp hn) = E.walkProfile p hn :=
  congrArg Word.profile (D.transferWalk_word E p hp hn)

end CCO.ProfileHelly.Network
