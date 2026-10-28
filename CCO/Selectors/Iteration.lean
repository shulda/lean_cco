import CCO.Selectors.Contraction
import Mathlib.SetTheory.Cardinal.Finite
import Lean.Elab.Tactic.Omega

/-! Finite strict gate descent, retaining the actual chain and its composition. -/
universe u v w a b
namespace CCO.Selectors

inductive RankedChain {State : Type a} (Edge : State → State → Type b)
    (rank : State → Nat) : State → State → Nat → Type (max a b) where
  | nil (J : State) : RankedChain Edge rank J J 0
  | cons {J K L : State} {n : Nat} (edge : Edge J K) (strict : rank K < rank J)
      (tail : RankedChain Edge rank K L n) : RankedChain Edge rank J L (n+1)

variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)

abbrev DescentChain (Good : ∀ {J K : Family S}, Contraction S J K → Prop) :=
  RankedChain (fun J K => { R : Contraction S J K // Good R }) (fun J => Nat.card J)

namespace DescentChain
variable {S} {Good : ∀ {J K : Family S}, Contraction S J K → Prop}

def composite {J K : Family S} {n : Nat} : DescentChain S Good J K n → Contraction S J K
  | .nil _ => Contraction.id _
  | .cons R _ tail => R.val.comp (composite tail)

theorem composite_good
    (hid : ∀ J, Good (Contraction.id (S := S) J))
    (hcomp : ∀ {J K L} (R : Contraction S J K) (T : Contraction S K L),
      Good R → Good T → Good (R.comp T))
    {J K : Family S} {n : Nat} (chain : DescentChain S Good J K n) :
    Good (composite chain) := by
  induction chain with
  | nil J => exact hid J
  | cons R _ tail ih => exact hcomp R.val (composite tail) R.property ih

end DescentChain

/-- Actual strict gates yield a terminal family and a bounded chain; `Good`
can retain the entire pure-tag covariance condition on the composite. -/
theorem finiteGateDescent (m : Nat) (Admissible Terminal : Family S → Prop)
    (lower : ∀ J, Admissible J → m ≤ Nat.card J)
    (Good : ∀ {J K : Family S}, Contraction S J K → Prop)
    (step : ∀ J, Admissible J → ¬Terminal J →
      ∃ K, Admissible K ∧ ∃ R : Contraction S J K, Good R ∧ Nat.card K < Nat.card J)
    (J : Family S) (hJ : Admissible J) :
    ∃ K, Admissible K ∧ Terminal K ∧ ∃ n, n ≤ Nat.card J - m ∧
      Nonempty (DescentChain S Good J K n) := by
  classical
  induction hn : Nat.card J using Nat.strong_induction_on generalizing J with
  | h n ih =>
    by_cases ht : Terminal J
    · exact ⟨J,hJ,ht,0,Nat.zero_le _,⟨.nil J⟩⟩
    · obtain ⟨K,hK,R,hR,hstrict⟩ := step J hJ ht
      obtain ⟨L,hL,htL,k,hk,⟨chain⟩⟩ := ih (Nat.card K) (by omega) K hK rfl
      refine ⟨L,hL,htL,k+1,?_,⟨.cons ⟨R,hR⟩ hstrict chain⟩⟩
      have hm := lower K hK
      omega

end CCO.Selectors
