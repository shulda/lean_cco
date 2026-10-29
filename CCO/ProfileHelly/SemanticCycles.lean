import CCO.ProfileHelly.Paths
import CCO.ProfileHelly.Semantics

/-! The semantic hypothesis is BOUND to one partial input and its actual
specified cycles. Each witness is a finite FULL allowed network; its map
may identify nonadjacent cycle occurrences. -/
universe u v z y
namespace CCO.ProfileHelly.Network
variable {ι : Type u} {T : Table.{u,v} ι} {V : Type z} {sort : V → ι}
variable (D : Network T sort)
open SimpleGraph

def CycleFeasible {x : V} (p : D.graph.Walk x x) (hp : ¬p.Nil) : Prop :=
  ∃ (W : Type z) (_ : Finite W) (targetSort : W → ι) (N : CompleteNetwork T targetSort)
    (q : N.toNetwork.Point (sort x)), Word.Realizes N.toNetwork (D.walkWord p hp) q q

def SemanticCycles : Prop :=
  ∀ (x : V) (p : D.graph.Walk x x) (hp : p.IsCycle), D.CycleFeasible p hp.not_nil

/-- C09: obtain the first cut at an ACTUAL diversity edge, then transport
the cut algebraically. Chosen arc terminals need not have distinct images. -/
theorem algebraic_of_semanticCycles (laws : TableLaws T) (cycles : D.SemanticCycles) :
    D.Algebraic := by
  intro x y hxy p q hd hpq
  have hcycle := D.disjoint_paths_cycle p q hd hpq
  obtain ⟨W,hW,targetSort,N,r,hr⟩ := cycles x (p.val.append q.val.reverse) hcycle
  have hp := Walk.not_nil_of_ne (p := p.val) hxy
  have hq := Walk.not_nil_of_ne (p := q.val) hxy
  have he := D.walkWord_append p.val q.val.reverse hp (D.reverse_not_nil q.val hq)
  rw [D.walkWord_reverse q.val hq] at he
  have hr' : Word.Realizes N.toNetwork
      ((D.walkWord p.val hp).append (D.walkWord q.val hq).reverse) r r := he ▸ hr
  exact Word.two_arc_readout laws N _ _ r hr'

theorem colour_of_tagged {i j} (x : D.Point i) (y : D.Point j) (a : T.Atom i j)
    (h : D.tagged x.val y.val = ⟨i,j,some a⟩) : D.colour x y = some a := by
  rcases x with ⟨x,rfl⟩
  rcases y with ⟨y,rfl⟩
  have h₁ := eq_of_heq (Sigma.mk.inj_iff.mp h).2
  exact eq_of_heq (Sigma.mk.inj_iff.mp h₁).2

namespace Hom
variable {W : Type y} {targetSort : W → ι} {E : Network T targetSort}
variable {D} (f : D.Hom E)

def pointTyped (x : V) : E.Point (sort x) := ⟨f.point x,f.sort_eq x⟩

theorem colour_preserved (x y : V) (a : T.Atom (sort x) (sort y))
    (ha : D.edge x y = some a) :
    E.colour (f.pointTyped x) (f.pointTyped y) = some a :=
  E.colour_of_tagged _ _ a (f.preserves x y a ha)

theorem realizes_walk {x y : V} (p : D.graph.Walk x y) (hp : ¬p.Nil) :
    Word.Realizes E (D.walkWord p hp) (f.pointTyped x) (f.pointTyped y) := by
  induction p with
  | nil => exact False.elim (hp .nil)
  | cons h p ih =>
    cases p with
    | nil => exact f.colour_preserved _ _ _ (D.label_spec h)
    | cons k p =>
      exact ⟨f.pointTyped _,f.colour_preserved _ _ _ (D.label_spec h),ih Walk.not_nil_cons⟩
end Hom

/-- C23: a genuine completion restricts to EVERY specified cycle. -/
theorem semanticCycles_of_hom {W : Type z} [Finite W] {targetSort : W → ι}
    (N : CompleteNetwork T targetSort) (f : D.Hom N.toNetwork) : D.SemanticCycles := by
  intro x p hp
  exact ⟨W,inferInstance,targetSort,N,f.pointTyped x,f.realizes_walk p hp.not_nil⟩

end CCO.ProfileHelly.Network
