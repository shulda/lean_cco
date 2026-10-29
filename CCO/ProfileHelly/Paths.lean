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

noncomputable def walkProfile {x y : V} (p : D.graph.Walk x y) (hp : ¬p.Nil) :
    T.Menu (sort x) (sort y) := (D.walkWord p hp).profile

theorem walkProfile_append (laws : TableLaws T) {x y z : V}
    (p : D.graph.Walk x y) (q : D.graph.Walk y z) (hp : ¬p.Nil) (hq : ¬q.Nil) :
    D.walkProfile (p.append q) (D.append_not_nil p q hp) =
      T.product (D.walkProfile p hp) (D.walkProfile q hq) := by
  rw [walkProfile,D.walkWord_append,Word.profile_append laws]
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

end CCO.ProfileHelly.Network
