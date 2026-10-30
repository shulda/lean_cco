import CCO.FiniteFibres.Boundaries.DifferenceSource
import CCO.FiniteFibres.Boundaries.GainWalk

/-! Actual finite partial difference-colour diagrams. The reverse colour is
the additive inverse; no symmetry or finite palette is assumed. All specified
simple cycles have actual target homomorphisms exactly when the whole diagram
does. Nonadjacent formal vertices are allowed to have equal images. -/
namespace CCO.FiniteFibres.Boundaries.Difference

variable (A V : Type*) [AddCommGroup A]

structure Diagram where
  edge : V → V → Option (Atom A)
  edge_self : ∀ x, edge x x = none
  edge_reverse : ∀ x y, edge y x = (edge x y).map (converse A)

namespace Diagram
variable {A V} (D : Diagram A V)

def graph : SimpleGraph V where
  Adj x y := ∃ a, D.edge x y = some a
  symm := ⟨by
    rintro x y ⟨a,ha⟩
    refine ⟨converse A a,?_⟩
    rw [D.edge_reverse,ha]
    rfl⟩
  loopless := ⟨by
    rintro x ⟨a,ha⟩
    rw [D.edge_self] at ha
    cases ha⟩

def weight (x y : V) : A := ((D.edge x y).map Subtype.val).getD 0

theorem weight_of_edge {x y : V} {a : Atom A} (h : D.edge x y = some a) :
    D.weight x y = a.val := by simp only [weight,h,Option.map_some,Option.getD_some]

theorem weight_reverse (x y : V) : D.weight y x = -D.weight x y := by
  unfold weight
  rw [D.edge_reverse]
  cases D.edge x y <;> simp [converse]

/-- A homomorphism of the WHOLE partially specified diagram into the actual
difference structure, with no injectivity conclusion. -/
def Hom (f : V → A) : Prop :=
  ∀ x y a, D.edge x y = some a → (source A).binary a (f x) (f y)

/-- One actual closed target walk spelling all the original cycle labels.
Values beyond the displayed finite length carry no constraints. -/
def CycleHom {x : V} (p : D.graph.Walk x x) : Prop :=
  ∃ f : ℕ → A, f p.length = f 0 ∧
    ∀ n < p.length, ∀ a,
      D.edge (p.getVert n) (p.getVert (n+1)) = some a →
        (source A).binary a (f n) (f (n+1))

theorem cycle_gain_zero {x : V} (p : D.graph.Walk x x) (h : D.CycleHom p) :
    GainWalk.gain D.weight p = 0 := by
  obtain ⟨f,hend,hf⟩ := h
  have hstep : ∀ n < p.length,
      D.weight (p.getVert n) (p.getVert (n+1)) = f (n+1)-f n := by
    intro n hn
    obtain ⟨a,ha⟩ := p.adj_getVert_succ hn
    rw [D.weight_of_edge ha]
    have hh := hf n hn a ha
    change f (n+1) = f n + a.val at hh
    rw [hh]
    abel
  rw [GainWalk.gain_of_getVert D.weight p f hstep,hend,sub_self]

/-- Semantic HOM CCO proved from genuine specified SIMPLE cycle requests,
through the proved repeated-vertex cancellation and global path integral.
The theorem even permits infinite formal graphs; finite instances are the
article's semantic CCO requests. -/
theorem hom_of_simple_cycles
    (hcycles : ∀ x (p : D.graph.Walk x x), p.IsCycle → D.CycleHom p) :
    ∃ f : V → A, D.Hom f := by
  have hclosed := GainWalk.closed_gain_zero D.weight D.weight_reverse
    (fun x p hp => D.cycle_gain_zero p (hcycles x p hp))
  obtain ⟨f,hf⟩ := GainWalk.exists_potential D.weight D.weight_reverse hclosed
  refine ⟨f,fun x y a ha => ?_⟩
  have hh := hf x y ⟨a,ha⟩
  rw [D.weight_of_edge ha] at hh
  change f y = f x + a.val
  rw [hh]
  abel

theorem cycles_of_hom {f : V → A} (h : D.Hom f) :
    ∀ x (p : D.graph.Walk x x), D.CycleHom p := by
  intro x p
  refine ⟨fun n => f (p.getVert n),?_,fun n hn a ha => h _ _ a ha⟩
  simp only [SimpleGraph.Walk.getVert_length,SimpleGraph.Walk.getVert_zero]

theorem hom_iff_simple_cycles :
    (∃ f : V → A, D.Hom f) ↔
      ∀ x (p : D.graph.Walk x x), p.IsCycle → D.CycleHom p :=
  ⟨fun ⟨f,hf⟩ x p _ => D.cycles_of_hom hf x p,D.hom_of_simple_cycles⟩

end Diagram

/-- This is semantic simple-cycle HOM CCO for the actual named difference
language. Each finite formal graph carries at most one specified atom per
ordered pair and the literal inverse converse. -/
def SemanticCCO : Prop :=
  ∀ (V : Type) [Finite V] (D : Diagram A V),
    (∀ x (p : D.graph.Walk x x), p.IsCycle → D.CycleHom p) →
      ∃ f : V → A, D.Hom f

theorem semanticCCO : SemanticCCO A := fun _ _ D => D.hom_of_simple_cycles

end CCO.FiniteFibres.Boundaries.Difference
