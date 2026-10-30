import CCO.APCharacter.Towers.FiniteUnary
import CCO.APCharacter.Towers.UnaryReduct
import CCO.APCharacter.Age.Category
import CCO.ParityHasse.Original.SourceHasse

/-! Actual CURRENT-source state for AP-only character iteration. New
canonical child sorts are sigma subtypes of the preceding named sorts;
carrier and atom subtypes retain all universe levels. No SAP field exists. -/
universe u v w t
namespace CCO.APCharacter.Towers
open ParityHasse.Original

structure CurrentSource where
  Sorts : Type u
  Point : Sorts → Type v
  source : AtomicSource.{u,v,w} Sorts Point
  G : Type t
  [group : Group G]
  [action : ∀ i, MulAction G (Point i)]
  homogeneous : HomogeneousSource source G
  countable : ∀ i, Countable (Point i)
  cco : SemanticCCO.{u,v,max u v,w} source

attribute [instance] CurrentSource.group CurrentSource.action

namespace CurrentSource
noncomputable section

/-- The ACTUAL current same-sort optional colour presentation is atomic;
its diversity atoms are realized, so finite tuple homogeneity recognizes
these names as the full pair orbitals used in the integer potential. -/
def potential (A : CurrentSource.{u,v,w,t}) : ℕ := by
  letI := A.source.finiteSort
  exact ∑ i : A.Sorts, 3 ^ Nat.card (A.source.Atom i i)

/-- A residual interval consists of ACTUAL original current invariant
equivalences and a genuinely finite nontrivial relative class. -/
def Obstruction (A : CurrentSource.{u,v,w,t}) : Prop :=
  ∃ (i : A.Sorts) (E F : ColourEq A.source i) (a : A.Point i),
    E < F ∧ Finite (RelativeClass E.val F.val a)

def Terminal (A : CurrentSource.{u,v,w,t}) : Prop := ¬A.Obstruction

/-- The actual finite OLD age category of this current source, with a
constant dummy zero bit. Every object has an actual induced realization;
all morphisms preserve the complete original name tables. -/
def finiteAge (A : CurrentSource.{u,v,w,t}) : UnaryAge.{0,0} where
  Obj := Age.Chart A.source (Age.zeroMask A.source)
  category := Age.chartCategory A.source (Age.zeroMask A.source)

/-- Target source fields already supply countability, homogeneity, full
finite original colour names, and semantic CCO. The step data additionally
certifies an ACTUAL unary expansion, rather than just rank arithmetic. -/
structure Step (age : CurrentSource.{u,v,w,t} → UnaryAge.{0,0})
    (A B : CurrentSource.{u,v,w,t}) where
  unary : UnaryTransition (age A) (age B)
  potential_lt : B.potential < A.potential

/-- One actual character step retains its literal unary projection and
its expansion functor TOGETHER, so an unrelated functor cannot stand in
for preservation of the original named reduct. -/
structure ActualStep (A B : CurrentSource.{u,v,w,t}) where
  reduct : UnaryReduct A.source B.source
  unary : UnaryTransition A.finiteAge B.finiteAge
  forget_eq : unary.forget = reduct.forget
  potential_lt : B.potential < A.potential

namespace ActualStep
noncomputable def toStep {A B : CurrentSource.{u,v,w,t}} (s : ActualStep A B) :
    Step finiteAge A B := ⟨s.unary,s.potential_lt⟩
end ActualStep

/-- Once the concrete source split has constructed its certificate for
EVERY current finite interval, the terminal source and the entire finite
old-to-new expansion tower are actual data. The concrete parity/SourceAge
consumer must discharge this progress input before the principal export. -/
theorem finite_terminalisation (age : CurrentSource.{u,v,w,t} → UnaryAge.{0,0})
    (split : ∀ A : CurrentSource.{u,v,w,t}, A.Obstruction →
      ∃ B, Nonempty (Step age A B)) (initial : CurrentSource.{u,v,w,t}) :
    ∃ terminal : CurrentSource.{u,v,w,t},
      ∃ history : History (fun A B => Nonempty (Step age A B)) initial terminal,
        terminal.Terminal ∧ history.length + terminal.potential ≤ initial.potential ∧
        Nonempty (UnaryTransition (age initial) (age terminal)) := by
  classical
  let Next := fun A B : CurrentSource.{u,v,w,t} => Nonempty (Step age A B)
  obtain ⟨terminal,h,ht,hbound⟩ := eliminate_obstructions Next potential Obstruction
    split (fun hs => (Classical.choice hs).potential_lt) initial
  refine ⟨terminal,h,ht,hbound,?_⟩
  exact ⟨finiteUnaryComposite age (fun hs => (Classical.choice hs).unary) h⟩

/-- The terminalisation interface specialized to the CONCRETE finite
source-age categories, with no caller-selected category representation. -/
theorem actual_age_terminalisation
    (split : ∀ A : CurrentSource.{u,v,w,t}, A.Obstruction →
      ∃ B, Nonempty (Step finiteAge A B)) (initial : CurrentSource.{u,v,w,t}) :
    ∃ terminal : CurrentSource.{u,v,w,t},
      ∃ history : History (fun A B => Nonempty (Step finiteAge A B)) initial terminal,
        terminal.Terminal ∧ history.length + terminal.potential ≤ initial.potential ∧
        Nonempty (UnaryTransition initial.finiteAge terminal.finiteAge) :=
  finite_terminalisation finiteAge split initial

/-- The actual old point/sort/colour projections compose along the same
finite source history. In particular their global old-reduct bijection is
retained even though the current carrier and named sorts change. -/
def historyReduct {A B : CurrentSource.{u,v,w,t}}
    (history : History (fun A B => Nonempty (ActualStep A B)) A B) :
    UnaryReduct A.source B.source := by
  classical
  induction history with
  | nil A => exact UnaryReduct.identity A.source
  | cons hs tail ih => exact (Classical.choice hs).reduct.compose ih

/-- Concrete ACTUAL steps produce a terminal current source together with
both its original reduct and its reasonable precompact expansion functor.
The original-to-terminal history preserves the relation between the two
at every step; no source or expansion provider is erased. -/
theorem actual_terminalisation
    (split : ∀ A : CurrentSource.{u,v,w,t}, A.Obstruction →
      ∃ B, Nonempty (ActualStep A B)) (initial : CurrentSource.{u,v,w,t}) :
    ∃ terminal : CurrentSource.{u,v,w,t},
      ∃ history : History (fun A B => Nonempty (ActualStep A B)) initial terminal,
        terminal.Terminal ∧ history.length + terminal.potential ≤ initial.potential ∧
        Nonempty (UnaryReduct initial.source terminal.source) ∧
        Nonempty (UnaryTransition initial.finiteAge terminal.finiteAge) := by
  classical
  let Next := fun A B : CurrentSource.{u,v,w,t} => Nonempty (ActualStep A B)
  obtain ⟨terminal,h,ht,hbound⟩ := eliminate_obstructions Next potential Obstruction
    split (fun hs => (Classical.choice hs).potential_lt) initial
  exact ⟨terminal,h,ht,hbound,⟨historyReduct h⟩,
    ⟨finiteUnaryComposite finiteAge (fun hs => (Classical.choice hs).unary) h⟩⟩

end
end CurrentSource
end CCO.APCharacter.Towers
