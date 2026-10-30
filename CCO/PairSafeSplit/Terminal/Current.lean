import CCO.APCharacter.SourceAge.SingleStep
import CCO.APCharacter.Towers.HistoryCoherence
import CCO.StrongExact.TriangleFullness

/-! B047 D10/D11 and C43--C50: actual current sources retain genuine SAP.
The accepted AP state is reused without changing its interface; this new
state stores old real SAP separately. Its FULL triangle age follows from
the actual homogeneous semantic CCO source, not an abstract table axiom. -/

universe u v w t z
namespace CCO.PairSafeSplit.Terminal
open APCharacter APCharacter.Towers ParityHasse.Original
noncomputable section

structure CurrentSource where
  base : APCharacter.Towers.CurrentSource.{u,v,w,t}
  sap : AgeSAP base.source

namespace CurrentSource

def potential (A : CurrentSource.{u,v,w,t}) : ℕ := A.base.potential
def Obstruction (A : CurrentSource.{u,v,w,t}) : Prop := A.base.Obstruction
def Terminal (A : CurrentSource.{u,v,w,t}) : Prop := A.base.Terminal

/-- Arbitrary finite formal-vertex universes retain the actual semantic
source property. The finite-reindexing proof is already accepted. -/
theorem semanticCCO (A : CurrentSource.{u,v,w,t}) :
    CCO.SemanticCCO.{u,v,z,w} A.base.source :=
  semanticCCO_change_universe A.base.source A.base.cco

/-- Every complete small-type-legal current network embeds inducedly.
This includes true singleton and pair admissibility and all empty cases. -/
theorem full_triangle_age (A : CurrentSource.{u,v,w,t})
    {V : Type z} (D : CompleteDiagram (S := A.base.source) V)
    (hsmall : D.SmallRealizable) :
    ∃ f : DiagramHom D.diagram, f.IsInjective :=
  D.triangleFullness_of_homogeneous_CCO A.base.homogeneous A.semanticCCO hsmall

/-- The actual whole current homogeneous action identifies each named
occurring diversity colour with one complete pair orbital. -/
theorem actual_pair_orbital (A : CurrentSource.{u,v,w,t})
    {i j : A.base.Sorts} (a : A.base.source.Atom i j) :
    ∃ x : A.base.Point i, ∃ y : A.base.Point j,
      A.base.source.atomRel a x y ∧
        A.base.source.atomRel a = GroupActions.orbital (G := A.base.G) x y :=
  A.base.source.diversity_atom_is_orbital_of_homogeneous A.base.homogeneous a

theorem named_sort_transitive (A : CurrentSource.{u,v,w,t}) (i : A.base.Sorts)
    (x y : A.base.Point i) : ∃ g : A.base.G, g • x = y :=
  A.base.source.original_sort_transitive_of_homogeneous A.base.homogeneous i x y

/-- Terminality rules out ALL finite relative intervals, not merely a
chosen exact sublattice. Thus every proper full invariant cover is infinite. -/
theorem terminal_interval_infinite (A : CurrentSource.{u,v,w,t})
    (ht : A.Terminal) {i : A.base.Sorts} (E F : ColourEq A.base.source i)
    (hEF : E < F) (a : A.base.Point i) :
    Infinite (RelativeClass E.val F.val a) := by
  apply not_finite_iff_infinite.mp
  intro hfin
  exact ht ⟨i,E,F,a,hEF,hfin⟩

theorem terminal_cover_infinite (A : CurrentSource.{u,v,w,t})
    (ht : A.Terminal) {i : A.base.Sorts} (E F : ColourEq A.base.source i)
    (hEF : E ⋖ F) (a : A.base.Point i) :
    Infinite (RelativeClass E.val F.val a) :=
  A.terminal_interval_infinite ht E F hEF.lt a

/-- A genuine safe source step carries the accepted literal old-reduct
projection and exactly the same reasonable/precompact forgetful functor. -/
structure ActualStep (A B : CurrentSource.{u,v,w,t}) where
  base : APCharacter.Towers.CurrentSource.ActualStep A.base B.base

namespace ActualStep
theorem potential_lt {A B : CurrentSource.{u,v,w,t}} (s : ActualStep A B) :
    B.potential < A.potential := s.base.potential_lt
end ActualStep

abbrev Next (A B : CurrentSource.{u,v,w,t}) := Nonempty (ActualStep A B)

/-- The actual safe history forgets only the extra retained-property
proofs; its vertices and original source steps are unchanged. -/
def baseHistory {A B : CurrentSource.{u,v,w,t}}
    (h : History Next A B) :
    History (fun A B => Nonempty (APCharacter.Towers.CurrentSource.ActualStep A B))
      A.base B.base := by
  induction h with
  | nil A => exact .nil A.base
  | cons hs tail ih => exact .cons ⟨(Classical.choice hs).base⟩ ih

theorem baseHistory_length {A B : CurrentSource.{u,v,w,t}}
    (h : History Next A B) : (baseHistory h).length = h.length := by
  induction h with
  | nil => rfl
  | cons hs tail ih => exact congrArg (fun n => n+1) ih

def historyReduct {A B : CurrentSource.{u,v,w,t}} (h : History Next A B) :
    UnaryReduct A.base.source B.base.source :=
  APCharacter.Towers.CurrentSource.historyReduct (baseHistory h)

def historyTransition {A B : CurrentSource.{u,v,w,t}} (h : History Next A B) :
    UnaryTransition A.base.finiteAge B.base.finiteAge :=
  APCharacter.Towers.CurrentSource.historyTransition (baseHistory h)

/-- The SAME composite functor has all three expansion properties; no
unrelated separately chosen reasonable functor replaces the literal reduct. -/
theorem history_forget_eq {A B : CurrentSource.{u,v,w,t}} (h : History Next A B) :
    (historyTransition h).forget = (historyReduct h).forget := rfl

theorem history_length_bound {A B : CurrentSource.{u,v,w,t}} (h : History Next A B) :
    h.length + B.potential ≤ A.potential :=
  History.length_bound potential (fun hs => (Classical.choice hs).potential_lt) h

theorem no_infinite_safe_splits (stage : ℕ → CurrentSource.{u,v,w,t})
    (next : ∀ n, Next (stage n) (stage (n+1))) : False :=
  no_infinite_steps Next potential (fun hs => (Classical.choice hs).potential_lt) stage next

end CurrentSource
end
end CCO.PairSafeSplit.Terminal
