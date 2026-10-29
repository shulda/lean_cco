import CCO.ProfileHelly.Words
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting

universe u v z y
namespace CCO.ProfileHelly
variable {ι : Type u} (T : Table.{u,v} ι)

/-- Partial atomic networks retain one fixed formal vertex set and sort map.
Missing edges have no imposed equality or inequality semantics. -/
structure Network {V : Type z} (sort : V → ι) where
  edge : ∀ x y, Option (T.Atom (sort x) (sort y))
  diagonal : ∀ x, edge x x = none
  edge_reverse : ∀ x y, (edge y x).map T.conv = edge x y

namespace Network
variable {T} {V : Type z} {sort : V → ι} (D : Network T sort)

def graph : SimpleGraph V where
  Adj x y := ∃ a, D.edge x y = some a
  symm := ⟨by
    rintro x y ⟨a,ha⟩
    exact ⟨T.conv a,by rw [← D.edge_reverse y x,ha]; rfl⟩⟩
  loopless := ⟨by
    rintro x ⟨a,ha⟩
    rw [D.diagonal] at ha
    cases ha⟩

noncomputable def label {x y : V} (h : D.graph.Adj x y) : T.Atom (sort x) (sort y) :=
  h.choose

theorem label_spec {x y : V} (h : D.graph.Adj x y) : D.edge x y = some (D.label h) :=
  h.choose_spec

theorem label_unique {x y : V} (h : D.graph.Adj x y) (a : T.Atom (sort x) (sort y))
    (ha : D.edge x y = some a) : D.label h = a :=
  Option.some.inj ((D.label_spec h).symm.trans ha)

theorem label_reverse {x y : V} (h : D.graph.Adj x y) :
    D.label h.symm = T.conv (D.label h) := by
  apply D.label_unique
  rw [← D.edge_reverse y x,D.label_spec h]
  rfl

/-- An extension retains EVERY old recorded edge on the SAME vertices and
the SAME sort map. This is stronger than a possibly colliding homomorphism. -/
def Extends (E : Network T sort) : Prop :=
  ∀ x y a, D.edge x y = some a → E.edge x y = some a

theorem Extends.refl : D.Extends D := fun _ _ _ h => h

theorem Extends.trans {E F : Network T sort} (h : D.Extends E) (k : E.Extends F) :
    D.Extends F := fun x y a ha => k x y a (h x y a ha)

def tagged (x y : V) : Σ i, Σ j, Option (T.Atom i j) := ⟨sort x,sort y,D.edge x y⟩

/-- Maps preserve actual named sorts and literal recorded diversity atoms;
only nonadjacent input vertices may collide. -/
structure Hom {W : Type y} {targetSort : W → ι} (E : Network T targetSort) where
  point : V → W
  sort_eq : ∀ x, targetSort (point x) = sort x
  preserves : ∀ x y a, D.edge x y = some a →
    E.tagged (point x) (point y) = ⟨sort x,sort y,some a⟩

end Network

/-- The FULL allowed class: completeness and exactly the distinct-vertex
table triangle tests, with no additional forbidden configurations. -/
structure CompleteNetwork {V : Type z} (sort : V → ι) extends Network T sort where
  complete : ∀ x y, x ≠ y → ∃ a, edge x y = some a
  legal : ∀ x y z, x ≠ y → y ≠ z → x ≠ z →
    ∀ a b c, edge x y = some a → edge y z = some b → edge x z = some c → T.triangle a b c

end CCO.ProfileHelly
