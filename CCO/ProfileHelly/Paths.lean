import CCO.ProfileHelly.Network
import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp

/-! Positive profiles of actual recorded walks and finite simple paths.
The cyclic invariant refers only to two internally disjoint simple arcs;
arbitrary overlapping path compatibility is derived separately. -/
universe u v z
namespace CCO.ProfileHelly.Network
variable {ι : Type u} {T : Table.{u,v} ι} {V : Type z} {sort : V → ι}
variable (D : Network T sort)
open SimpleGraph

noncomputable def walkWord : {x y : V} → (p : D.graph.Walk x y) →
    ¬p.Nil → Word T (sort x) (sort y)
  | _,_,.nil,h => False.elim (h .nil)
  | _,_,.cons h .nil,_ => .single (D.label h)
  | _,_,.cons h (.cons k p),_ => .cons (D.label h) (walkWord (.cons k p) Walk.not_nil_cons)

theorem walkWord_length {x y : V} (p : D.graph.Walk x y) (hp : ¬p.Nil) :
    (D.walkWord p hp).length = p.length := by
  induction p with
  | nil => exact False.elim (hp .nil)
  | cons h p ih =>
    cases p with
    | nil => rfl
    | cons k p =>
      exact congrArg (· + 1) (ih Walk.not_nil_cons)

theorem append_not_nil {x y z : V} (p : D.graph.Walk x y) (q : D.graph.Walk y z)
    (hp : ¬p.Nil) : ¬(p.append q).Nil :=
  fun h => hp ((Walk.nil_append_iff).mp h).1

theorem walkWord_append {x y z : V} (p : D.graph.Walk x y) (q : D.graph.Walk y z)
    (hp : ¬p.Nil) (hq : ¬q.Nil) :
    D.walkWord (p.append q) (D.append_not_nil p q hp) =
      (D.walkWord p hp).append (D.walkWord q hq) := by
  induction p with
  | nil => exact False.elim (hp .nil)
  | cons h p ih =>
    cases p with
    | nil =>
      cases q with
      | nil => exact False.elim (hq .nil)
      | cons k q => rfl
    | cons k p =>
      change Word.cons (D.label h) _ = Word.cons (D.label h) _
      exact congrArg (Word.cons (D.label h)) (ih q Walk.not_nil_cons hq)

theorem walkWord_cons {x y z : V} (h : D.graph.Adj x y) (p : D.graph.Walk y z)
    (hp : ¬p.Nil) : D.walkWord (.cons h p) Walk.not_nil_cons =
      Word.cons (D.label h) (D.walkWord p hp) := by
  cases p with
  | nil => exact False.elim (hp .nil)
  | cons _ _ => rfl

theorem reverse_not_nil {x y : V} (p : D.graph.Walk x y) (hp : ¬p.Nil) :
    ¬p.reverse.Nil := fun h => hp (Walk.nil_reverse.mp h)

theorem walkWord_congr {x y : V} {p q : D.graph.Walk x y} (he : p = q)
    (hp : ¬p.Nil) (hq : ¬q.Nil) : D.walkWord p hp = D.walkWord q hq := by
  cases he
  rfl

theorem walkWord_reverse {x y : V} (p : D.graph.Walk x y) (hp : ¬p.Nil) :
    D.walkWord p.reverse (D.reverse_not_nil p hp) = (D.walkWord p hp).reverse := by
  induction p with
  | nil => exact False.elim (hp .nil)
  | cons h p ih =>
    cases p with
    | nil =>
      change Word.single (D.label h.symm) = Word.single (T.conv (D.label h))
      rw [D.label_reverse]
    | cons k p =>
      calc
        D.walkWord (Walk.cons h (Walk.cons k p)).reverse _ =
            D.walkWord ((Walk.cons k p).reverse.append h.symm.toWalk)
              (D.append_not_nil _ _ (D.reverse_not_nil _ Walk.not_nil_cons)) :=
          D.walkWord_congr (Walk.reverse_cons _ _) _ _
        _ = (D.walkWord (Walk.cons k p).reverse _).append (Word.single (D.label h.symm)) :=
          D.walkWord_append (Walk.cons k p).reverse h.symm.toWalk
            (D.reverse_not_nil _ Walk.not_nil_cons) Walk.not_nil_cons
        _ = (D.walkWord (Walk.cons h (Walk.cons k p)) hp).reverse := by
          rw [ih Walk.not_nil_cons]
          change (D.walkWord (Walk.cons k p) Walk.not_nil_cons).reverse.append (Word.single (D.label h.symm)) =
            (D.walkWord (Walk.cons k p) Walk.not_nil_cons).reverse.append (Word.single (T.conv (D.label h)))
          rw [D.label_reverse]

noncomputable def walkProfile {x y : V} (p : D.graph.Walk x y) (hp : ¬p.Nil) :
    T.Menu (sort x) (sort y) := (D.walkWord p hp).profile

theorem walkProfile_congr {x y : V} {p q : D.graph.Walk x y} (he : p = q)
    (hp : ¬p.Nil) (hq : ¬q.Nil) : D.walkProfile p hp = D.walkProfile q hq :=
  congrArg Word.profile (D.walkWord_congr he hp hq)

theorem walkProfile_append (laws : TableLaws T) {x y z : V}
    (p : D.graph.Walk x y) (q : D.graph.Walk y z) (hp : ¬p.Nil) (hq : ¬q.Nil) :
    D.walkProfile (p.append q) (D.append_not_nil p q hp) =
      T.product (D.walkProfile p hp) (D.walkProfile q hq) := by
  rw [walkProfile,D.walkWord_append,Word.profile_append laws]
  rfl

theorem walkProfile_reverse (laws : TableLaws T) {x y : V}
    (p : D.graph.Walk x y) (hp : ¬p.Nil) :
    D.walkProfile p.reverse (D.reverse_not_nil p hp) = T.opposite (D.walkProfile p hp) := by
  rw [walkProfile,D.walkWord_reverse,Word.profile_reverse laws]
  rfl

noncomputable def pathProfile {x y : V} (hxy : x ≠ y) (p : D.graph.Path x y) :
    T.Menu (sort x) (sort y) := D.walkProfile p.val (Walk.not_nil_of_ne hxy)

theorem pathProfile_nonempty (laws : TableLaws T) {x y : V}
    (hxy : x ≠ y) (p : D.graph.Path x y) : (D.pathProfile hxy p).Nonempty :=
  Word.profile_nonempty laws _

noncomputable def internal {x y : V} (p : D.graph.Walk x y) : Finset V := by
  classical
  exact (p.support.toFinset.erase x).erase y

@[simp] theorem mem_internal {x y a : V} (p : D.graph.Walk x y) :
    a ∈ D.internal p ↔ a ∈ p.support ∧ a ≠ x ∧ a ≠ y := by
  classical
  simp only [internal,Finset.mem_erase,List.mem_toFinset]
  tauto

/-- Algebraic simple-cycle compatibility in its two-positive-arcs form.
Only internally disjoint DISTINCT geometric paths are tested here. -/
def Algebraic : Prop :=
  ∀ (x y : V) (hxy : x ≠ y) (p q : D.graph.Path x y),
    Disjoint (D.internal p.val) (D.internal q.val) → p ≠ q →
      (D.pathProfile hxy p ∩ D.pathProfile hxy q).Nonempty

theorem simple_paths_finite [Finite V] (x y : V) : Finite (D.graph.Path x y) := by
  classical
  let : Fintype V := Fintype.ofFinite V
  infer_instance

/-- Two distinct internally disjoint simple arcs form an ACTUAL simple
cycle. The two one-edge paths coincide and are therefore excluded. -/
theorem disjoint_paths_cycle {x y : V} (p q : D.graph.Path x y)
    (hd : Disjoint (D.internal p.val) (D.internal q.val)) (hne : p ≠ q) :
    (p.val.append q.val.reverse).IsCycle := by
  classical
  have hno : ¬∃ a, a ∈ p.val.support ∧ a ∈ q.val.support ∧ a ≠ x ∧ a ≠ y := by
    rintro ⟨a,hap,haq,hax,hay⟩
    exact Finset.disjoint_left.mp hd ((D.mem_internal _).mpr ⟨hap,hax,hay⟩)
      ((D.mem_internal _).mpr ⟨haq,hax,hay⟩)
  have hpq : p.val ≠ q.val := fun h => hne (Subtype.ext h)
  refine p.property.isCycle_append q.property.reverse (fun a ha hb => ?_) ?_
  · grind [Walk.dropLast_support_concat,SimpleGraph.Walk.IsPath.support_nodup,
      Walk.support_reverse,Walk.cons_tail_support]
  · grind [Walk.length_reverse,Walk.eq_of_length_le_one]

noncomputable def prefixPath [DecidableEq V] {x y a : V} (p : D.graph.Path x y) (ha : a ∈ p.val.support) :
    D.graph.Path x a := ⟨p.val.takeUntil a ha,p.property.takeUntil ha⟩

noncomputable def suffixPath [DecidableEq V] {x y a : V} (p : D.graph.Path x y) (ha : a ∈ p.val.support) :
    D.graph.Path a y := ⟨p.val.dropUntil a ha,p.property.dropUntil ha⟩

theorem prefix_suffix_profile [DecidableEq V] (laws : TableLaws T) {x y a : V}
    (hxy : x ≠ y) (hxa : x ≠ a) (hay : a ≠ y) (p : D.graph.Path x y)
    (ha : a ∈ p.val.support) :
    D.pathProfile hxy p = T.product (D.pathProfile hxa (D.prefixPath p ha))
      (D.pathProfile hay (D.suffixPath p ha)) := by
  classical
  have he := D.walkProfile_append laws (p.val.takeUntil a ha) (p.val.dropUntil a ha)
    (Walk.not_nil_of_ne hxa) (Walk.not_nil_of_ne hay)
  have hc := D.walkProfile_congr (Walk.take_spec p.val ha)
    (D.append_not_nil _ _ (Walk.not_nil_of_ne hxa)) (Walk.not_nil_of_ne hxy)
  exact hc.symm.trans he

end CCO.ProfileHelly.Network
