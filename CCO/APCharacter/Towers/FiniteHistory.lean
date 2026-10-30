import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega

/-! Finite current-source iteration. Every step is indexed by its ACTUAL
source and target; the terminal condition is tested on the current target,
not on an initial source or an asserted limiting object. -/
universe u
namespace CCO.APCharacter.Towers
variable {State : Type u} (Step : State → State → Prop)

inductive History : State → State → Type u
  | nil (a : State) : History a a
  | cons {a b c : State} : Step a b → History b c → History a c

namespace History
variable {Step}
def length {a b : State} : History Step a b → ℕ
  | .nil _ => 0
  | .cons _ tail => tail.length + 1

def append {a b c : State} : History Step a b → History Step b c → History Step a c
  | .nil _, tail => tail
  | .cons h t, tail => .cons h (t.append tail)

@[simp] theorem length_append {a b c : State} (s : History Step a b) (t : History Step b c) :
    (s.append t).length = s.length + t.length := by
  induction s with
  | nil => simp [append,length]
  | cons h s ih => simp only [append,length,ih]; omega

/-- Every source invariant retained by each actual step is retained by
its entire finite history; no additional endpoint provider is assumed. -/
theorem preserves (P : State → Prop)
    (retains : ∀ {a b}, Step a b → P a → P b) {a b : State}
    (history : History Step a b) (initial : P a) : P b := by
  induction history with
  | nil => exact initial
  | cons h tail ih => exact ih (retains h initial)

/-- Strict integer descent bounds the NUMBER of nontrivial stages. -/
theorem length_bound (rank : State → ℕ)
    (descends : ∀ {a b}, Step a b → rank b < rank a)
    {a b : State} (history : History Step a b) :
    history.length + rank b ≤ rank a := by
  induction history with
  | nil => simp [length]
  | cons h tail ih =>
    have hlt := descends h
    simp only [length]
    omega
end History

/-- A residual finite interval must provide a next actual strict-descent
step. Once those source instances are supplied, stopping is forced to be
at a terminal CURRENT source, with an explicit finite original-to-terminal
history and a bound by its initial integer potential. -/
theorem exists_terminal (rank : State → ℕ) (Terminal : State → Prop)
    (progress : ∀ a, ¬Terminal a → ∃ b, Step a b)
    (descends : ∀ {a b}, Step a b → rank b < rank a) (initial : State) :
    ∃ terminal, ∃ history : History Step initial terminal,
      Terminal terminal ∧ history.length + rank terminal ≤ rank initial := by
  classical
  have all : ∀ n : ℕ, ∀ a : State, rank a = n →
      ∃ b, ∃ history : History Step a b,
        Terminal b ∧ history.length + rank b ≤ rank a := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro a ha
      by_cases hterm : Terminal a
      · exact ⟨a,.nil a,hterm,by simp [History.length]⟩
      · obtain ⟨b,hab⟩ := progress a hterm
        have hlt : rank b < n := ha ▸ descends hab
        obtain ⟨c,tail,hc,hbound⟩ := ih (rank b) hlt b rfl
        exact ⟨c,.cons hab tail,hc,History.length_bound rank descends (.cons hab tail)⟩
  exact all (rank initial) initial rfl

/-- The same theorem with explicit residual obstruction data. The absence
of a split is not silently declared terminal: every actual obstruction must
construct a next step. -/
theorem eliminate_obstructions (rank : State → ℕ) (Obstruction : State → Prop)
    (split : ∀ a, Obstruction a → ∃ b, Step a b)
    (descends : ∀ {a b}, Step a b → rank b < rank a) (initial : State) :
    ∃ terminal, ∃ history : History Step initial terminal,
      ¬Obstruction terminal ∧ history.length + rank terminal ≤ rank initial := by
  classical
  apply exists_terminal Step rank (fun a => ¬Obstruction a) _ descends initial
  intro a h
  exact split a (not_not.mp h)

end CCO.APCharacter.Towers
